package io.shiftleft.fuzzyc2cpg

import org.slf4j.LoggerFactory
import java.nio.file.Files
import java.util.concurrent.ConcurrentHashMap

import better.files.File
import io.shiftleft.codepropertygraph.Cpg
import io.shiftleft.fuzzyc2cpg.passes.{AstCreationPass, CMetaDataPass, StubRemovalPass, TypeNodePass}
import io.shiftleft.passes.IntervalKeyPool
import io.shiftleft.semanticcpg.passes.CfgCreationPass
import io.shiftleft.x2cpg.SourceFiles
import overflowdb.{Config, Graph, Node}
import org.json4s._
import org.json4s.native.JsonMethods._
import scala.io.Source

import scala.collection.mutable.ListBuffer
import scala.util.control.NonFatal

case class Global(usedTypes: ConcurrentHashMap[String, Boolean] = new ConcurrentHashMap[String, Boolean]())

class FuzzyC2Cpg() {
  import FuzzyC2Cpg.logger
  val BASE_ID = 1000100

  def runWithPreprocessorAndOutput(sourcePaths: Set[String],
                                   sourceFileExtensions: Set[String],
                                   includeFiles: Set[String],
                                   includePaths: Set[String],
                                   defines: Set[String],
                                   undefines: Set[String],
                                   preprocessorExecutable: String,
                                   optionalOutputPath: Option[String] = None): Unit = {
    // Create temp dir to store preprocessed source.
    val preprocessedPath = Files.createTempDirectory("fuzzyc2cpg_preprocessed_")
    logger.info(s"Writing preprocessed files to [$preprocessedPath]")

    val preprocessorLogFile = Files.createTempFile("fuzzyc2cpg_preprocessor_log", ".txt").toFile
    logger.info(s"Writing preprocessor logs to [$preprocessorLogFile]")

    val sourceFileNames = SourceFiles.determine(sourcePaths, sourceFileExtensions)

    val commandBuffer = new ListBuffer[String]()
    commandBuffer.appendAll(List(preprocessorExecutable, "--verbose", "-o", preprocessedPath.toString))
    if (sourceFileNames.nonEmpty) commandBuffer.appendAll(List("-f", sourceFileNames.mkString(",")))
    if (includeFiles.nonEmpty) commandBuffer.appendAll(List("--include", includeFiles.mkString(",")))
    if (includePaths.nonEmpty) commandBuffer.appendAll(List("-I", includePaths.mkString(",")))
    if (defines.nonEmpty) commandBuffer.appendAll(List("-D", defines.mkString(",")))
    if (undefines.nonEmpty) commandBuffer.appendAll(List("-U", defines.mkString(",")))

    val cmd = commandBuffer.toList

    // Run preprocessor
    logger.info("Running preprocessor...")
    val process = new ProcessBuilder()
      .redirectOutput(preprocessorLogFile)
      .redirectError(preprocessorLogFile)
      .command(cmd: _*)
      .start()
    val exitCode = process.waitFor()

    if (exitCode == 0) {
      logger.info(s"Preprocessing complete, files written to [$preprocessedPath], starting CPG generation...")
      val cpg = runAndOutput(Set(preprocessedPath.toString), sourceFileExtensions, optionalOutputPath)
      cpg.close()
    } else {
      logger.error(
        s"Error occurred whilst running preprocessor. Log written to [$preprocessorLogFile]. Exit code [$exitCode].")
    }
  }

  def printNodes(graph: Graph): Unit = {
    println("Nodes: " + graph.nodeCount())
    val itr = graph.nodes()
    while(itr.hasNext) {
      val node = itr.next()
      println("summary: " + node)
      println("id: " + node.id())
      println("label: " + node.label())
      println("propertyKeys: " + node.propertyKeys())
      println("propertyMap: " + node.propertyMap())
      println("")
    }
  }

  def printEdges(graph: Graph): Unit = {
    println("Edges:" + graph.edgeCount())
    val itrEdges = graph.edges()
    while(itrEdges.hasNext) {
      val edge = itrEdges.next()
      println(edge)

      val innerItr = edge.bothNodes()
      while(innerItr.hasNext)
        println(innerItr.next())

      println("")
    }
  }

  def getField(jsonObject: JsonAST.JValue, attributeName: String) = {
    jsonObject.findField(jfield => {jfield._1.equals(attributeName)}).get._2.values
  }

  def getFieldWrapped(jsonObject: JsonAST.JValue, attributeName: String) = {
    jsonObject.findField(jfield => {jfield._1.equals(attributeName)}).get._2
  }

  def getFieldString(jsonObject: JsonAST.JValue, attributeName: String): String = {
    getField(jsonObject, attributeName).toString
  }

  def getFieldInt(jsonObject: JsonAST.JValue, attributeName: String): Int = {
    getFieldString(jsonObject, attributeName).toInt
  }

  def getFieldBoolean(jsonObject: JsonAST.JValue, attributeName: String): Boolean = {
    getField(jsonObject, attributeName).equals(true)
  }

  def getFieldList(jsonObject: JsonAST.JValue, attributeName: String): List[Object] = {
    getField(jsonObject, attributeName).asInstanceOf[List[Object]]
  }

  def registerFunction(graph: Graph, wrappedFunction: JsonAST.JValue): Unit = {
    val functionId = getFieldInt(wrappedFunction, "id")
    val functionAttributesWrapped = getFieldWrapped(wrappedFunction, "attributes")

    val functionName = getFieldString(functionAttributesWrapped, "name")
    val isImplemented = getFieldBoolean(functionAttributesWrapped, "implemented")

    // Ignore unimplemented functions.
    if(!isImplemented) {
      return
    }

    require(getFieldString(functionAttributesWrapped, "kind").equals("function"))

    graph.addNode(BASE_ID + functionId, "METHOD")
    graph.node(BASE_ID + functionId).setProperty("COLUMN_NUMBER", 0)
    graph.node(BASE_ID + functionId).setProperty("LINE_NUMBER", 0)
    graph.node(BASE_ID + functionId).setProperty("COLUMN_NUMBER_END", 0)
    graph.node(BASE_ID + functionId).setProperty("IS_EXTERNAL", false)
    graph.node(BASE_ID + functionId).setProperty("SIGNATURE", "int main (int,char * [ ])")
    graph.node(BASE_ID + functionId).setProperty("NAME", functionName)
    graph.node(BASE_ID + functionId).setProperty("AST_PARENT_TYPE", "")
    graph.node(BASE_ID + functionId).setProperty("AST_PARENT_FULL_NAME", "")
    graph.node(BASE_ID + functionId).setProperty("ORDER", -1)
    graph.node(BASE_ID + functionId).setProperty("CODE", "main (int argc,char *argv[])")
    graph.node(BASE_ID + functionId).setProperty("FULL_NAME", functionName)
    graph.node(BASE_ID + functionId).setProperty("LINE_NUMBER_END", 0)
    graph.node(BASE_ID + functionId).setProperty("FILENAME", "")

    graph.node(1000101).addEdge("AST", graph.node(BASE_ID + functionId))

    val functionComponentsWrapped = getFieldWrapped(wrappedFunction, "children")
    val functionComponents = getFieldList(wrappedFunction, "children")
    val parameterListComponent = functionComponentsWrapped.children(0)
    val parameterList2Component = functionComponentsWrapped.children(1) // TODO: could be return values?
    val bodyComponent = functionComponents(2)

    // Deal with function parameters.
    println("---------")
    println(parameterListComponent.values)
    val parameterList = parameterListComponent.values.asInstanceOf[Map[String, List[Object]]]
    var order = 1
    for(attributeSpecificObject <- parameterList("children")) {
      val attributeSpecificMap = attributeSpecificObject.asInstanceOf[Map[String, Object]]
      val parameterId = attributeSpecificMap("id").toString.toInt
      val attributeMap = attributeSpecificMap("attributes").asInstanceOf[Map[String, Object]]
      val parameterName = attributeMap("name").toString
      val parameterType = attributeMap("type").toString

      graph.addNode(BASE_ID + parameterId, "METHOD_PARAMETER_IN")
      graph.node(BASE_ID + parameterId).setProperty("ORDER", order)
      graph.node(BASE_ID + parameterId).setProperty("CODE", parameterType + " " + parameterName)
      graph.node(BASE_ID + parameterId).setProperty("COLUMN_NUMBER", 0)
      graph.node(BASE_ID + parameterId).setProperty("LINE_NUMBER", 0)
      graph.node(BASE_ID + parameterId).setProperty("TYPE_FULL_NAME", parameterType)
      graph.node(BASE_ID + parameterId).setProperty("EVALUATION_STRATEGY", "BY_VALUE")
      graph.node(BASE_ID + parameterId).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
      graph.node(BASE_ID + parameterId).setProperty("NAME", parameterName)

      graph.node(BASE_ID + functionId).addEdge("AST", graph.node(BASE_ID + parameterId))

      order += 1
    }

    graph.addNode(2*BASE_ID + functionId, "METHOD_RETURN")
    graph.node(2*BASE_ID + functionId).setProperty("ORDER", 4)
    graph.node(2*BASE_ID + functionId).setProperty("CODE", "RET")
    graph.node(2*BASE_ID + functionId).setProperty("COLUMN_NUMBER", 0)
    graph.node(2*BASE_ID + functionId).setProperty("LINE_NUMBER", 0)
    graph.node(2*BASE_ID + functionId).setProperty("TYPE_FULL_NAME", "int") // TODO
    graph.node(2*BASE_ID + functionId).setProperty("EVALUATION_STRATEGY", "BY_VALUE")
    graph.node(2*BASE_ID + functionId).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())

    graph.node(BASE_ID + functionId).addEdge("AST", graph.node(2*BASE_ID + functionId))

    println(functionId)
    println(functionName)

    // Deal with function body.
    val blockId = registerBlock(graph, bodyComponent.asInstanceOf[Map[String, Object]])
    graph.node(BASE_ID + functionId).addEdge("AST", graph.node(BASE_ID + blockId))

    //val childrenElement = getField(wrappedFunction, "children")
    //println(childrenElement)

  }

  def registerBlock(graph: Graph, block: Map[String, Object]): Int = {
    println(block("name"))
    require(block("name").asInstanceOf[String].equals("Block"))

    val blockId = block("id").toString.toInt
    println("block id:")
    println(blockId)
    graph.addNode(BASE_ID + blockId, "BLOCK")
    graph.node(BASE_ID + blockId).setProperty("ORDER", 3)
    graph.node(BASE_ID + blockId).setProperty("ARGUMENT_INDEX", 3)
    graph.node(BASE_ID + blockId).setProperty("CODE", "")
    graph.node(BASE_ID + blockId).setProperty("COLUMN_NUMBER", 0)
    graph.node(BASE_ID + blockId).setProperty("TYPE_FULL_NAME", "void")
    graph.node(BASE_ID + blockId).setProperty("LINE_NUMBER", 0)
    graph.node(BASE_ID + blockId).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())

    val statementsList = block("children").asInstanceOf[List[Object]]
    println("statementsList:")
    println(statementsList)
    println("statementsList length:")
    println(statementsList.length)
    for(statement <- statementsList) {
      val statementIds = registerStatement(graph, statement)
      for(statementId <- statementIds) {
        graph.node(BASE_ID + blockId).addEdge("AST", graph.node(BASE_ID + statementId))
      }
    }
    println(statementsList.length)

    blockId
  }

  def registerStatement(graph: Graph, statement: Object): Array[Int] = {
    val statementMap = statement.asInstanceOf[Map[String, Object]]
    println(statementMap)
    val statementName = statementMap("name").toString
    println("Statement name: " + statementName)
    val statementId = statementMap("id").toString.toInt
    println("Statement ID: " + statementId)

    if(statementName.equals("Literal") || statementName.equals("Identifier")) {
      val statementAttributes = statementMap("attributes").asInstanceOf[Map[String, Object]]
      graph.addNode(BASE_ID + statementId, (if (statementName.equals("Identifier")) "IDENTIFIER" else "LITERAL"))
      graph.node(BASE_ID + statementId).setProperty("ORDER", 2)
      graph.node(BASE_ID + statementId).setProperty("ARGUMENT_INDEX", 2)
      graph.node(BASE_ID + statementId).setProperty("CODE", statementAttributes("value").toString)
      graph.node(BASE_ID + statementId).setProperty("COLUMN_NUMBER", 0)
      graph.node(BASE_ID + statementId).setProperty("TYPE_FULL_NAME", statementAttributes("type").toString)
      graph.node(BASE_ID + statementId).setProperty("LINE_NUMBER", 0)
      graph.node(BASE_ID + statementId).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
      if (statementName.equals("Identifier")) {
        graph.node(BASE_ID + statementId).setProperty("NAME", statementAttributes("value").toString)
        val referencedId = statementAttributes("referencedDeclaration").toString.toInt
        if(graph.node(BASE_ID + referencedId) != null) // TODO: Remove when supporting global variables.
          graph.node(BASE_ID + statementId).addEdge("REF", graph.node(BASE_ID + referencedId))
      }

      return Array(statementId)
    }

    val statementChildren = statementMap("children").asInstanceOf[List[Map[String, Object]]]
    println("Number of statement children: " + statementChildren.length)

    // The CPG AST does not seem to know about tuple expressions,
    // so their children get passed right through.
    if(statementName.equals("TupleExpression")) {
      println("Processing tuple expression")
      require(statementChildren.length == 1)

      return registerStatement(graph, statementChildren(0))
    }

    if(!statementName.equals("ExpressionStatement") && !statementName.equals("Block")
      && !statementName.equals("IfStatement") && !statementName.equals("WhileStatement")
      && !statementName.equals("ForStatement") && !statementName.equals("BinaryOperation")
      && !statementName.equals("VariableDeclarationStatement")) {
      println("panic!!! unknown statement with statement name: " + statementName)
      return Array()
    }

    val operationId = statementId
    if(statementName.equals("Block")) {
      val blockId = registerBlock(graph, statementMap)
      return Array(blockId)
    }

    if(statementName.equals("BinaryOperation")) {
      val statementAttributes = statementMap("attributes").asInstanceOf[Map[String, Object]]
      val statementDataType = statementAttributes("type").toString

      val operatorName = getBinaryOperatorName(statementAttributes("operator").toString)

      graph.addNode(BASE_ID + operationId, "CALL")
      graph.node(BASE_ID + operationId).setProperty("ORDER", 1)
      graph.node(BASE_ID + operationId).setProperty("ARGUMENT_INDEX", 1)
      graph.node(BASE_ID + operationId).setProperty("CODE", "")
      graph.node(BASE_ID + operationId).setProperty("COLUMN_NUMBER", 0)
      graph.node(BASE_ID + operationId).setProperty("METHOD_FULL_NAME", operatorName)
      graph.node(BASE_ID + operationId).setProperty("TYPE_FULL_NAME", "ANY")
      graph.node(BASE_ID + operationId).setProperty("LINE_NUMBER", 0)
      graph.node(BASE_ID + operationId).setProperty("DISPATCH_TYPE", "STATIC_DISPATCH")
      graph.node(BASE_ID + operationId).setProperty("SIGNATURE", "TODO assignment signature")
      graph.node(BASE_ID + operationId).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
      graph.node(BASE_ID + operationId).setProperty("NAME", operatorName)

      val idLeftChild = registerStatement(graph, statementChildren(0))(0)
      val idRightChild = registerStatement(graph, statementChildren(1))(0)

      graph.node(BASE_ID + operationId).addEdge("ARGUMENT", graph.node(BASE_ID + idLeftChild))
      graph.node(BASE_ID + operationId).addEdge("ARGUMENT", graph.node(BASE_ID + idRightChild))

      graph.node(BASE_ID + operationId).addEdge("AST", graph.node(BASE_ID + idLeftChild))
      graph.node(BASE_ID + operationId).addEdge("AST", graph.node(BASE_ID + idRightChild))

      return Array(operationId)
    }

    val operationName = statementChildren(0)("name").toString

    if(statementName.equals("VariableDeclarationStatement")) {
      val variableAttributes = statementChildren(0)("attributes").asInstanceOf[Map[String, Object]]
      val variableDataType = variableAttributes("type").toString
      val variableName = variableAttributes("name").toString

      val declarationOperationId = statementChildren(0)("id").toString.toInt
      val assignmentOperationId = statementChildren(1)("id").toString.toInt

      println("Handling VariableDeclarationStatement")
      require(operationName.equals("VariableDeclaration"))
      println(variableAttributes)
      println(variableDataType)
      println(variableName)
      println(declarationOperationId)
      println(assignmentOperationId)

      graph.addNode(BASE_ID + declarationOperationId, "LOCAL")
      graph.node(BASE_ID + declarationOperationId).setProperty("TYPE_FULL_NAME", variableDataType)
      graph.node(BASE_ID + declarationOperationId).setProperty("ORDER", 1)
      graph.node(BASE_ID + declarationOperationId).setProperty("CODE", variableName)
      graph.node(BASE_ID + declarationOperationId).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
      graph.node(BASE_ID + declarationOperationId).setProperty("NAME", variableName)

      val assignmentAttributes = statementChildren(1)("attributes").asInstanceOf[Map[String, Object]]
      val rightVariableName = assignmentAttributes("value").toString
      val rightKindName = statementChildren(1)("name").toString

      println("entering assignment helper")
      // We need more nodes than the Solidity AST provides. Therefore, instead of declarationOperationId, 1*BASE_ID + declarationOperationId is passed in.
      // The reason that we need more nodes is that the CPG AST requires you to link to an Identifier Node which in turn links to the Local node. You cannot link
      // to a Local node directly via an argument edge.
      assignmentHelper(graph, operationId, variableDataType, 1*BASE_ID + declarationOperationId, assignmentOperationId, variableName, rightVariableName, rightKindName, assignmentAttributes)
      println("exited assignment helper")
      graph.node(BASE_ID + (1*BASE_ID + declarationOperationId)).addEdge("REF", graph.node(BASE_ID + declarationOperationId))


      return Array(declarationOperationId, operationId)
    }

    val operationAttributes = statementChildren(0)("attributes").asInstanceOf[Map[String, Object]]

    if(statementName.equals("IfStatement") || statementName.equals("WhileStatement")
      || statementName.equals("ForStatement")) {
      graph.addNode(BASE_ID + operationId, "CONTROL_STRUCTURE")
      graph.node(BASE_ID + operationId).setProperty("PARSER_TYPE_NAME", statementName)
      graph.node(BASE_ID + operationId).setProperty("ORDER", 1)
      graph.node(BASE_ID + operationId).setProperty("LINE_NUMBER", 0)
      graph.node(BASE_ID + operationId).setProperty("ARGUMENT_INDEX", 1)
      graph.node(BASE_ID + operationId).setProperty("CODE", "")
      graph.node(BASE_ID + operationId).setProperty("COLUMN_NUMBER", 0)

      if(statementName.equals("IfStatement") || statementName.equals("WhileStatement")) {
        val conditionId = registerStatement(graph, statementChildren(0))(0)
        // There never are several action IDs. This is because in Solidity,
        // variable delarations in an if's or loop's body is illegal unless that
        // body is a block.
        val actionId = registerStatement(graph, statementChildren(1))(0)

        graph.node(BASE_ID + operationId).addEdge("CONDITION", graph.node(BASE_ID + conditionId))
        graph.node(BASE_ID + operationId).addEdge("AST", graph.node(BASE_ID + conditionId))
        graph.node(BASE_ID + operationId).addEdge("AST", graph.node(BASE_ID + actionId))
      } else {
        println("REGISTERING FOR STATEMENT")
        val initialActionIds = registerStatement(graph, statementChildren(0))
        val conditionId = registerStatement(graph, statementChildren(1))(0)
        val incrementId = registerStatement(graph, statementChildren(2))(0)
        val actionId = registerStatement(graph, statementChildren(3))(0)
        println("REGISTERED FOR STATEMENT")
        // Weird order bc that's the order that the CPG AST uses.
        graph.node(BASE_ID + operationId).addEdge("CONDITION", graph.node(BASE_ID + conditionId))
        for(initialActionId <- initialActionIds)
          graph.node(BASE_ID + operationId).addEdge("AST", graph.node(BASE_ID + initialActionId))
        graph.node(BASE_ID + operationId).addEdge("AST", graph.node(BASE_ID + conditionId))
        graph.node(BASE_ID + operationId).addEdge("AST", graph.node(BASE_ID + incrementId))
        graph.node(BASE_ID + operationId).addEdge("AST", graph.node(BASE_ID + actionId))
      }
      return Array(operationId)
    }

    val operationDataType = operationAttributes("type").toString

    statementName match {
      case "ExpressionStatement" => {
        println("Operation name: " + operationName)

        val operationChildren = statementChildren(0)("children").asInstanceOf[List[Object]]

        if(operationName.equals("UnaryOperation")) {
          val operationAttributes = statementChildren(0)("attributes").asInstanceOf[Map[String, Object]]

          val operatorSymbol = operationAttributes("operator").toString
          val isPrefixOperator = operationAttributes("prefix").equals(true)
          val symbol = operationChildren(0).asInstanceOf[Map[String, Object]]("attributes").asInstanceOf[Map[String, Object]]("value").toString

          val code = if(isPrefixOperator) operatorSymbol + symbol else symbol + operatorSymbol

          val operatorName = getUnaryOperatorName(operatorSymbol, isPrefixOperator)

          graph.addNode(BASE_ID + operationId, "CALL")
          graph.node(BASE_ID + operationId).setProperty("ORDER", 1)
          graph.node(BASE_ID + operationId).setProperty("ARGUMENT_INDEX", 1)
          graph.node(BASE_ID + operationId).setProperty("CODE", code)
          graph.node(BASE_ID + operationId).setProperty("COLUMN_NUMBER", 0)
          graph.node(BASE_ID + operationId).setProperty("METHOD_FULL_NAME", operatorName)
          graph.node(BASE_ID + operationId).setProperty("TYPE_FULL_NAME", "ANY")
          graph.node(BASE_ID + operationId).setProperty("LINE_NUMBER", 0)
          graph.node(BASE_ID + operationId).setProperty("DISPATCH_TYPE", "STATIC_DISPATCH")
          graph.node(BASE_ID + operationId).setProperty("SIGNATURE", "TODO assignment signature")
          graph.node(BASE_ID + operationId).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
          graph.node(BASE_ID + operationId).setProperty("NAME", operatorName)

          val idChild = registerStatement(graph, operationChildren(0))(0)
          println("my child is:")
          println(graph.node(BASE_ID + idChild))
          graph.node(BASE_ID + operationId).addEdge("ARGUMENT", graph.node(BASE_ID + idChild))
          graph.node(BASE_ID + operationId).addEdge("AST", graph.node(BASE_ID + idChild))

          return Array(operationId)
        }

        val statementLeftId = operationChildren(0).asInstanceOf[Map[String, Object]]("id").toString.toInt
        val statementRightId = operationChildren(1).asInstanceOf[Map[String, Object]]("id").toString.toInt
        val statementRightKindName = operationChildren(1).asInstanceOf[Map[String, Object]]("name").toString

        val statementLeftHandSide = operationChildren(0).asInstanceOf[Map[String, Object]]("attributes").asInstanceOf[Map[String, Object]]
        val statementRightHandSide = operationChildren(1).asInstanceOf[Map[String, Object]]("attributes").asInstanceOf[Map[String, Object]]

        operationName match {
          case "Assignment" => {
            println("Handling Assignment")
            require(operationAttributes("operator").toString.equals("="))
            require(operationChildren.length == 2)

            println(statementLeftId + " <- " + statementRightId)

            val statementLeftReferencedId = statementLeftHandSide("referencedDeclaration").toString.toInt
            val statementLeftVariableName = statementLeftHandSide("value").toString
            val statementRightVariableName = statementRightHandSide("value").toString

            assignmentHelper(graph, operationId, operationDataType, statementLeftId, statementRightId, statementLeftVariableName, statementRightVariableName, statementRightKindName, statementRightHandSide)
          }
          case "FunctionCall" => {
            println("function calls are not yet implemented")
            // TODO
          }
          case _ => {
            println("unknown operation")
          }
        }
      }
    }

    Array(operationId)
  }

  def assignmentHelper(graph: Graph, operationId: Int, operationDataType: String, statementLeftId: Int, statementRightId: Int, statementLeftVariableName: String, statementRightVariableName: String, statementRightKindName: String, statementRightHandSide: Map[String, Object]): Unit = {
    // TODO: store assignment nodes / edges / properties / whatever there is to store
    graph.addNode(BASE_ID + operationId, "CALL")
    graph.node(BASE_ID + operationId).setProperty("ORDER", 1)
    graph.node(BASE_ID + operationId).setProperty("ARGUMENT_INDEX", 1)
    graph.node(BASE_ID + operationId).setProperty("CODE", statementLeftVariableName + " = " + statementRightVariableName)
    graph.node(BASE_ID + operationId).setProperty("COLUMN_NUMBER", 0)
    graph.node(BASE_ID + operationId).setProperty("METHOD_FULL_NAME", "<operator>.assignment")
    graph.node(BASE_ID + operationId).setProperty("TYPE_FULL_NAME", "ANY")
    graph.node(BASE_ID + operationId).setProperty("LINE_NUMBER", 0)
    graph.node(BASE_ID + operationId).setProperty("DISPATCH_TYPE", "STATIC_DISPATCH")
    graph.node(BASE_ID + operationId).setProperty("SIGNATURE", "TODO assignment signature")
    graph.node(BASE_ID + operationId).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
    graph.node(BASE_ID + operationId).setProperty("NAME", "<operator>.assignment")

    graph.addNode(BASE_ID + statementLeftId, "IDENTIFIER")
    graph.node(BASE_ID + statementLeftId).setProperty("ORDER", 1)
    graph.node(BASE_ID + statementLeftId).setProperty("ARGUMENT_INDEX", 1)
    graph.node(BASE_ID + statementLeftId).setProperty("CODE", statementLeftVariableName)
    graph.node(BASE_ID + statementLeftId).setProperty("COLUMN_NUMBER", 0)
    graph.node(BASE_ID + statementLeftId).setProperty("TYPE_FULL_NAME", operationDataType)
    graph.node(BASE_ID + statementLeftId).setProperty("LINE_NUMBER", 0)
    graph.node(BASE_ID + statementLeftId).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
    graph.node(BASE_ID + statementLeftId).setProperty("NAME", statementLeftVariableName)

    graph.addNode(BASE_ID + statementRightId, (if (statementRightKindName.equals("Identifier")) "IDENTIFIER" else "LITERAL"))
    graph.node(BASE_ID + statementRightId).setProperty("ORDER", 2)
    graph.node(BASE_ID + statementRightId).setProperty("ARGUMENT_INDEX", 2)
    graph.node(BASE_ID + statementRightId).setProperty("CODE", statementRightVariableName)
    graph.node(BASE_ID + statementRightId).setProperty("COLUMN_NUMBER", 0)
    graph.node(BASE_ID + statementRightId).setProperty("TYPE_FULL_NAME", operationDataType) // Set to operationDataType instead fo "type" from "attributes" so it also works for literals. The latter would be something like "int_const 7" for literals.
    graph.node(BASE_ID + statementRightId).setProperty("LINE_NUMBER", 0)
    graph.node(BASE_ID + statementRightId).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
    if (statementRightKindName.equals("Identifier"))
      graph.node(BASE_ID + statementRightId).setProperty("NAME", statementRightVariableName)

    graph.node(BASE_ID + operationId).addEdge("AST", graph.node(BASE_ID + statementLeftId))
    graph.node(BASE_ID + operationId).addEdge("ARGUMENT", graph.node(BASE_ID + statementLeftId))

    graph.node(BASE_ID + operationId).addEdge("AST", graph.node(BASE_ID + statementRightId))
    graph.node(BASE_ID + operationId).addEdge("ARGUMENT", graph.node(BASE_ID + statementRightId))

    // TODO: comment back in after including global variables
    // graph.node(BASE_ID + statementLeftId).addEdge("REF", graph.node(BASE_ID + statementLeftReferencedId))

    if (statementRightKindName.equals("Identifier")) {
      val statementRightReferencedId = statementRightHandSide("referencedDeclaration").toString.toInt
      graph.node(BASE_ID + statementRightId).addEdge("REF", graph.node(BASE_ID + statementRightReferencedId))
    }
  }

  def registerVariable(graph: Graph, wrappedFunction: JsonAST.JValue): Unit = {
    // The AST this repo uses does not seem to care about global variables.
  }

  def getBinaryOperatorName(symbol: String): String = {
    // This switch contains all simple binary operators found in:
    // schema/src/main/resources/schemas/operators.json
    // The operators not supported by Solidity are commented out.
    // Unary operators are commented out too.
    // Some assignment operators are not included. These use a plural s in
    // the angle brackets:
    // "name":"<operators>.assignmentExponentiation"
    // "name":"<operators>.assignmentModulo"
    // "name":"<operators>.assignmentShiftLeft"
    // "name":"<operators>.assignmentLogicalShiftRight"
    // "name":"<operators>.assignmentArithmeticShiftRight"
    // "name":"<operators>.assignmentAnd"
    // "name":"<operators>.assignmentOr"
    // "name":"<operators>.assignmentXor"
    // I have no idea why these have a plural s but the difference scares me,
    // so I left them out.
    symbol match {
      case "+" => "<operator>.addition"
      case "-" => "<operator>.subtraction"
      case "*" => "<operator>.multiplication"
      case "/" => "<operator>.division"
      case "**" => "<operator>.exponentiation"
      case "%" => "<operator>.modulo"
      case "<<" => "<operator>.shiftLeft"
      // case "" => "<operator>.logicalShiftRight"
      case ">>" => "<operator>.arithmeticShiftRight"
      case "~" => "<operator>.not"
      case "&" => "<operator>.and"
      case "|" => "<operator>.or"
      case "^" => "<operator>.xor"
      /*
      // Assignments are not considered binary operations by Solidity.
      case "+=" => "<operator>.assignmentPlus"
      case "-=" => "<operator>.assignmentMinus"
      case "*=" => "<operator>.assignmentMultiplication"
      case "/=" => "<operator>.assignmentDivision"
      case "=" => "<operator>.assignment"
      */
      case "||" => "<operator>.logicalOr"
      case "&&" => "<operator>.logicalAnd"
      case "==" => "<operator>.equals"
      case "!=" => "<operator>.notEquals"
      case ">" => "<operator>.greaterThan"
      case "<" => "<operator>.lessThan"
      case ">=" => "<operator>.greaterEqualsThan"
      case "<=" => "<operator>.lessEqualsThan"
      // These either don't exist in Solidity or are not considered
      // binary operations.
      /*
      case "" => "<operator>.instanceOf"
      case "" => "<operator>.memberAccess"
      case "" => "<operator>.indirectMemberAccess"
      case "" => "<operator>.computedMemberAccess"
      case "" => "<operator>.indirectComputedMemberAccess"
      case "" => "<operator>.indirection"
      case "" => "<operator>.delete"
      case "" => "<operator>.conditional"
      case "" => "<operator>.cast"
      case "" => "<operator>.compare"
      case "" => "<operator>.addressOf"
      case "" => "<operator>.sizeOf"
      case "" => "<operator>.fieldAccess"
      case "" => "<operator>.indirectFieldAccess"
      case "" => "<operator>.indexAccess"
      case "" => "<operator>.indirectIndexAccess"
      case "" => "<operator>.pointerShift"
      case "" => "<operator>.getElementPtr"
      */
      case _ => "<operator>.ERROR"
    }
  }

    def getUnaryOperatorName(symbol: String, prefix: Boolean): String = {
      // This switch contains all unary operators found in:
      // schema/src/main/resources/schemas/operators.json
      symbol match {
        case "-" => "<operator>.minus"
        case "+" => "<operator>.plus"
        case "++" => if(prefix) "<operator>.preIncrement" else "<operator>.postIncrement"
        case "--" => if(prefix) "<operator>.preDecrement" else "<operator>.postDecrement"
        case "!" => "<operator>.logicalNot"
        case _ => "<operator>.ERROR"
      }
  }

  def runAndOutput(sourcePaths: Set[String],
                   sourceFileExtensions: Set[String],
                   optionalOutputPath: Option[String] = None): Cpg = {
    println("source paths: " + sourcePaths)
    println("source file extensions: " + sourceFileExtensions)
    println("optional output path: " + optionalOutputPath)
    val metaDataKeyPool = new IntervalKeyPool(1, 100)
    val typesKeyPool = new IntervalKeyPool(100, 1000100)
    val functionKeyPools = KeyPools.obtain(2, 1000101)

    val cpg = initCpg(optionalOutputPath)
    val sourceFileNames = SourceFiles.determine(sourcePaths, sourceFileExtensions)

    new CMetaDataPass(cpg, Some(metaDataKeyPool)).createAndApply()
    val graph = cpg.graph
    //printNodes(graph)
    //printEdges(graph)

    val useSolidity = true

    if(!useSolidity) {
      val astCreator = new AstCreationPass(sourceFileNames, cpg, functionKeyPools.head)
      astCreator.createAndApply() // MARK
    } else {
        /*
      // MARK: Einstiegspunkt
      // The first 4 nodes are: MetaData, NamespaceBlock, File, NamespaceBlock
      // All other nodes need to be deleted.
      var itr = cpg.graph.nodes()
      val nodesToDelete = new Array[Node](cpg.graph.nodeCount()-4)
      for(i <- 0 until cpg.graph.nodeCount()) {
        if(i >= 4) {
          nodesToDelete(i-4) = itr.next()
        } else {
          itr.next()
        }
      }
      for(node <- nodesToDelete) {
        //println(node.)
        cpg.graph.remove(node)
      }
      // TODO: Wieso wird die AST-Edge von "io.shiftleft.codepropertygraph.generated.nodes.NamespaceBlock[label=NAMESPACE_BLOCK; id=1000101]" zu
      // TODO: "io.shiftleft.codepropertygraph.generated.nodes.Method[label=METHOD; id=1000102]" nicht entfernt, obwohl der Ziel-Knoten entfernt wird?
  */

        graph.addNode(1000100, "FILE")
        graph.addNode(1000101, "NAMESPACE_BLOCK")

        graph.node(1000100).setProperty("ORDER", -1)
        graph.node(1000100).setProperty("NAME", "/home/christoph/.applications/x42/c/X42.c")

        graph.node(1000101).setProperty("FULL_NAME", "/home/christoph/.applications/x42/c/X42.c:<global>")
        graph.node(1000101).setProperty("ORDER", -1)
        graph.node(1000101).setProperty("FILENAME", "")
        graph.node(1000101).setProperty("NAME", "<global>")

        graph.node(1000100).addEdge("AST", graph.node(1000101))

        val fileContents = Source.fromFile("/home/christoph/.applications/codepropertygraph/solcAsts/ast8.json").getLines.mkString
        val originalAst = parse(fileContents)

        /*childrenOpt match {
        case Some(children) => println(children._2)
        case None => println("no children")
      }*/

        val contractLevel = originalAst.findField((jfield) => {
          jfield._1.equals("children")
        }).get._2
          .children(0).findField((jfield) => {
          jfield._1.equals("children")
        }).get._2
          .children
        println(contractLevel)
        println(contractLevel.length)

        contractLevel.foreach(wrappedContractLevelElement => {
          // This is equivalent to this JS code:
          // let name = wrappedContractLevelElement.name
          val name = wrappedContractLevelElement.findField(jfield => {
            jfield._1.equals("name")
          }).get._2.values.toString

          name match {
            case "FunctionDefinition" => registerFunction(graph, wrappedContractLevelElement)
            case "VariableDeclaration" => registerVariable(graph, wrappedContractLevelElement)
          }
        })
        println("processing completed")
        /*
      // Recreating the initial CPG manually.
      graph.addNode(1000100, "FILE")
      graph.addNode(1000101, "NAMESPACE_BLOCK")
      graph.addNode(1000102, "METHOD")
      graph.addNode(1000103, "METHOD_PARAMETER_IN")
      graph.addNode(1000104, "METHOD_PARAMETER_IN")
      graph.addNode(1000105, "BLOCK")
      graph.addNode(1000106, "CONTROL_STRUCTURE")
      graph.addNode(1000107, "CALL")
      graph.addNode(1000108, "CALL")
      graph.addNode(1000109, "IDENTIFIER")
      graph.addNode(1000110, "LITERAL")
      graph.addNode(1000111, "CALL")
      graph.addNode(1000112, "CALL")
      graph.addNode(1000113, "CALL")
      graph.addNode(1000114, "IDENTIFIER")
      graph.addNode(1000115, "LITERAL")
      graph.addNode(1000116, "LITERAL")
      graph.addNode(1000117, "LITERAL")
      graph.addNode(1000118, "BLOCK")
      graph.addNode(1000119, "CALL")
      graph.addNode(1000120, "IDENTIFIER")
      graph.addNode(1000121, "LITERAL")
      graph.addNode(1000122, "CALL")
      graph.addNode(1000123, "LITERAL")
      graph.addNode(1000124, "CALL")
      graph.addNode(1000125, "LITERAL")
      graph.addNode(1000126, "CALL")
      graph.addNode(1000127, "LITERAL")
      graph.addNode(1000128, "METHOD_RETURN")

      graph.node(1000100).setProperty("ORDER", -1)
      graph.node(1000100).setProperty("NAME", "/home/christoph/.applications/x42/c/X42.c")

      graph.node(1000101).setProperty("FULL_NAME", "/home/christoph/.applications/x42/c/X42.c:<global>")
      graph.node(1000101).setProperty("ORDER", -1)
      graph.node(1000101).setProperty("FILENAME", "")
      graph.node(1000101).setProperty("NAME", "<global>")

      graph.node(1000102).setProperty("COLUMN_NUMBER", 0)
      graph.node(1000102).setProperty("LINE_NUMBER", 5)
      graph.node(1000102).setProperty("COLUMN_NUMBER_END", 0)
      graph.node(1000102).setProperty("IS_EXTERNAL", false)
      graph.node(1000102).setProperty("SIGNATURE", "int main (int,char * [ ])")
      graph.node(1000102).setProperty("NAME", "main")
      graph.node(1000102).setProperty("AST_PARENT_TYPE", "")
      graph.node(1000102).setProperty("AST_PARENT_FULL_NAME", "")
      graph.node(1000102).setProperty("ORDER", -1)
      graph.node(1000102).setProperty("CODE", "main (int argc,char *argv[])")
      graph.node(1000102).setProperty("FULL_NAME", "main")
      graph.node(1000102).setProperty("LINE_NUMBER_END", 12)
      graph.node(1000102).setProperty("FILENAME", "")

      graph.node(1000103).setProperty("ORDER", 1)
      graph.node(1000103).setProperty("CODE", "int argc")
      graph.node(1000103).setProperty("COLUMN_NUMBER", 9)
      graph.node(1000103).setProperty("LINE_NUMBER", 5)
      graph.node(1000103).setProperty("TYPE_FULL_NAME", "int")
      graph.node(1000103).setProperty("EVALUATION_STRATEGY", "BY_VALUE")
      graph.node(1000103).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
      graph.node(1000103).setProperty("NAME", "argc")

      graph.node(1000104).setProperty("ORDER", 2)
      graph.node(1000104).setProperty("CODE", "char *argv[]")
      graph.node(1000104).setProperty("COLUMN_NUMBER", 19)
      graph.node(1000104).setProperty("LINE_NUMBER", 5)
      graph.node(1000104).setProperty("TYPE_FULL_NAME", "char * [ ]")
      graph.node(1000104).setProperty("EVALUATION_STRATEGY", "BY_VALUE")
      graph.node(1000104).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
      graph.node(1000104).setProperty("NAME", "argv")

      graph.node(1000105).setProperty("ORDER", 3)
      graph.node(1000105).setProperty("ARGUMENT_INDEX", 3)
      graph.node(1000105).setProperty("CODE", "")
      graph.node(1000105).setProperty("COLUMN_NUMBER", 33)
      graph.node(1000105).setProperty("TYPE_FULL_NAME", "void")
      graph.node(1000105).setProperty("LINE_NUMBER", 5)
      graph.node(1000105).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())

      graph.node(1000106).setProperty("PARSER_TYPE_NAME", "IfStatement")
      graph.node(1000106).setProperty("ORDER", 1)
      graph.node(1000106).setProperty("LINE_NUMBER", 6)
      graph.node(1000106).setProperty("ARGUMENT_INDEX", 1)
      graph.node(1000106).setProperty("CODE", "if (argc > 1 && strcmp(argv[1], \"42\") == 0)")
      graph.node(1000106).setProperty("COLUMN_NUMBER", 2)

      graph.node(1000107).setProperty("ORDER", 1)
      graph.node(1000107).setProperty("ARGUMENT_INDEX", 1)
      graph.node(1000107).setProperty("CODE", "argc > 1 && strcmp(argv[1], \"42\") == 0")
      graph.node(1000107).setProperty("COLUMN_NUMBER", 6)
      graph.node(1000107).setProperty("METHOD_FULL_NAME", "<operator>.logicalAnd")
      graph.node(1000107).setProperty("TYPE_FULL_NAME", "ANY")
      graph.node(1000107).setProperty("LINE_NUMBER", 6)
      graph.node(1000107).setProperty("DISPATCH_TYPE", "STATIC_DISPATCH")
      graph.node(1000107).setProperty("SIGNATURE", "TODO assignment signature")
      graph.node(1000107).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
      graph.node(1000107).setProperty("NAME", "<operator>.logicalAnd")

      graph.node(1000108).setProperty("ORDER", 1)
      graph.node(1000108).setProperty("ARGUMENT_INDEX", 1)
      graph.node(1000108).setProperty("CODE", "argc > 1")
      graph.node(1000108).setProperty("COLUMN_NUMBER", 6)
      graph.node(1000108).setProperty("METHOD_FULL_NAME", "<operator>.greaterThan")
      graph.node(1000108).setProperty("TYPE_FULL_NAME", "ANY")
      graph.node(1000108).setProperty("LINE_NUMBER", 6)
      graph.node(1000108).setProperty("DISPATCH_TYPE", "STATIC_DISPATCH")
      graph.node(1000108).setProperty("SIGNATURE", "TODO assignment signature")
      graph.node(1000108).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
      graph.node(1000108).setProperty("NAME", "<operator>.greaterThan")

      graph.node(1000109).setProperty("ORDER", 1)
      graph.node(1000109).setProperty("ARGUMENT_INDEX", 1)
      graph.node(1000109).setProperty("CODE", "argc")
      graph.node(1000109).setProperty("COLUMN_NUMBER", 6)
      graph.node(1000109).setProperty("TYPE_FULL_NAME", "int")
      graph.node(1000109).setProperty("LINE_NUMBER", 6)
      graph.node(1000109).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
      graph.node(1000109).setProperty("NAME", "argc")

      graph.node(1000110).setProperty("ORDER", 2)
      graph.node(1000110).setProperty("ARGUMENT_INDEX", 2)
      graph.node(1000110).setProperty("CODE", "1")
      graph.node(1000110).setProperty("COLUMN_NUMBER", 13)
      graph.node(1000110).setProperty("TYPE_FULL_NAME", "int")
      graph.node(1000110).setProperty("LINE_NUMBER", 6)
      graph.node(1000110).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())

      graph.node(1000111).setProperty("ORDER", 2)
      graph.node(1000111).setProperty("ARGUMENT_INDEX", 2)
      graph.node(1000111).setProperty("CODE", "strcmp(argv[1], \"42\") == 0")
      graph.node(1000111).setProperty("COLUMN_NUMBER", 18)
      graph.node(1000111).setProperty("METHOD_FULL_NAME", "<operator>.equals")
      graph.node(1000111).setProperty("TYPE_FULL_NAME", "ANY")
      graph.node(1000111).setProperty("LINE_NUMBER", 6)
      graph.node(1000111).setProperty("DISPATCH_TYPE", "STATIC_DISPATCH")
      graph.node(1000111).setProperty("SIGNATURE", "TODO assignment signature")
      graph.node(1000111).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
      graph.node(1000111).setProperty("NAME", "<operator>.equals")

      graph.node(1000112).setProperty("ORDER", 1)
      graph.node(1000112).setProperty("ARGUMENT_INDEX", 1)
      graph.node(1000112).setProperty("CODE", "strcmp(argv[1], \"42\")")
      graph.node(1000112).setProperty("COLUMN_NUMBER", 18)
      graph.node(1000112).setProperty("METHOD_FULL_NAME", "strcmp")
      graph.node(1000112).setProperty("TYPE_FULL_NAME", "ANY")
      graph.node(1000112).setProperty("LINE_NUMBER", 6)
      graph.node(1000112).setProperty("DISPATCH_TYPE", "STATIC_DISPATCH")
      graph.node(1000112).setProperty("SIGNATURE", "TODO assignment signature")
      graph.node(1000112).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
      graph.node(1000112).setProperty("NAME", "strcmp")

      graph.node(1000113).setProperty("ORDER", 1)
      graph.node(1000113).setProperty("ARGUMENT_INDEX", 1)
      graph.node(1000113).setProperty("CODE", "argv[1]")
      graph.node(1000113).setProperty("COLUMN_NUMBER", 25)
      graph.node(1000113).setProperty("METHOD_FULL_NAME", "<operator>.indirectIndexAccess")
      graph.node(1000113).setProperty("TYPE_FULL_NAME", "ANY")
      graph.node(1000113).setProperty("LINE_NUMBER", 6)
      graph.node(1000113).setProperty("DISPATCH_TYPE", "STATIC_DISPATCH")
      graph.node(1000113).setProperty("SIGNATURE", "TODO assignment signature")
      graph.node(1000113).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
      graph.node(1000113).setProperty("NAME", "<operator>.indirectIndexAccess")

      graph.node(1000114).setProperty("ORDER", 1)
      graph.node(1000114).setProperty("ARGUMENT_INDEX", 1)
      graph.node(1000114).setProperty("CODE", "argv")
      graph.node(1000114).setProperty("COLUMN_NUMBER", 25)
      graph.node(1000114).setProperty("TYPE_FULL_NAME", "char * [ ]")
      graph.node(1000114).setProperty("LINE_NUMBER", 6)
      graph.node(1000114).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
      graph.node(1000114).setProperty("NAME", "argv")

      graph.node(1000115).setProperty("ORDER", 2)
      graph.node(1000115).setProperty("ARGUMENT_INDEX", 2)
      graph.node(1000115).setProperty("CODE", "1")
      graph.node(1000115).setProperty("COLUMN_NUMBER", 30)
      graph.node(1000115).setProperty("TYPE_FULL_NAME", "int")
      graph.node(1000115).setProperty("LINE_NUMBER", 6)
      graph.node(1000115).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())

      graph.node(1000116).setProperty("ORDER", 2)
      graph.node(1000116).setProperty("ARGUMENT_INDEX", 2)
      graph.node(1000116).setProperty("CODE", "\"42\"")
      graph.node(1000116).setProperty("COLUMN_NUMBER", 34)
      graph.node(1000116).setProperty("TYPE_FULL_NAME", "char *")
      graph.node(1000116).setProperty("LINE_NUMBER", 6)
      graph.node(1000116).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())

      graph.node(1000117).setProperty("ORDER", 2)
      graph.node(1000117).setProperty("ARGUMENT_INDEX", 2)
      graph.node(1000117).setProperty("CODE", "0")
      graph.node(1000117).setProperty("COLUMN_NUMBER", 43)
      graph.node(1000117).setProperty("TYPE_FULL_NAME", "int")
      graph.node(1000117).setProperty("LINE_NUMBER", 6)
      graph.node(1000117).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())

      graph.node(1000118).setProperty("ORDER", 2)
      graph.node(1000118).setProperty("ARGUMENT_INDEX", 2)
      graph.node(1000118).setProperty("CODE", "")
      graph.node(1000118).setProperty("COLUMN_NUMBER", 46)
      graph.node(1000118).setProperty("TYPE_FULL_NAME", "void")
      graph.node(1000118).setProperty("LINE_NUMBER", 6)
      graph.node(1000118).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())

      graph.node(1000119).setProperty("ORDER", 1)
      graph.node(1000119).setProperty("ARGUMENT_INDEX", 1)
      graph.node(1000119).setProperty("CODE", "fprintf(stderr, \"It depends!\\n\")")
      graph.node(1000119).setProperty("COLUMN_NUMBER", 4)
      graph.node(1000119).setProperty("METHOD_FULL_NAME", "fprintf")
      graph.node(1000119).setProperty("TYPE_FULL_NAME", "ANY")
      graph.node(1000119).setProperty("LINE_NUMBER", 7)
      graph.node(1000119).setProperty("DISPATCH_TYPE", "STATIC_DISPATCH")
      graph.node(1000119).setProperty("SIGNATURE", "TODO assignment signature")
      graph.node(1000119).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
      graph.node(1000119).setProperty("NAME", "fprintf")

      graph.node(1000120).setProperty("ORDER", 1)
      graph.node(1000120).setProperty("ARGUMENT_INDEX", 1)
      graph.node(1000120).setProperty("CODE", "stderr")
      graph.node(1000120).setProperty("COLUMN_NUMBER", 12)
      graph.node(1000120).setProperty("TYPE_FULL_NAME", "ANY")
      graph.node(1000120).setProperty("LINE_NUMBER", 7)
      graph.node(1000120).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
      graph.node(1000120).setProperty("NAME", "stderr")

      graph.node(1000121).setProperty("ORDER", 2)
      graph.node(1000121).setProperty("ARGUMENT_INDEX", 2)
      graph.node(1000121).setProperty("CODE", "\"It depends!\\n\"")
      graph.node(1000121).setProperty("COLUMN_NUMBER", 20)
      graph.node(1000121).setProperty("TYPE_FULL_NAME", "char *")
      graph.node(1000121).setProperty("LINE_NUMBER", 7)
      graph.node(1000121).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())

      graph.node(1000122).setProperty("ORDER", 2)
      graph.node(1000122).setProperty("ARGUMENT_INDEX", 2)
      graph.node(1000122).setProperty("CODE", "exit(42)")
      graph.node(1000122).setProperty("COLUMN_NUMBER", 4)
      graph.node(1000122).setProperty("METHOD_FULL_NAME", "exit")
      graph.node(1000122).setProperty("TYPE_FULL_NAME", "ANY")
      graph.node(1000122).setProperty("LINE_NUMBER", 8)
      graph.node(1000122).setProperty("DISPATCH_TYPE", "STATIC_DISPATCH")
      graph.node(1000122).setProperty("SIGNATURE", "TODO assignment signature")
      graph.node(1000122).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
      graph.node(1000122).setProperty("NAME", "exit")

      graph.node(1000123).setProperty("ORDER", 1)
      graph.node(1000123).setProperty("ARGUMENT_INDEX", 1)
      graph.node(1000123).setProperty("CODE", "42")
      graph.node(1000123).setProperty("COLUMN_NUMBER", 9)
      graph.node(1000123).setProperty("TYPE_FULL_NAME", "int")
      graph.node(1000123).setProperty("LINE_NUMBER", 8)
      graph.node(1000123).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())

      graph.node(1000124).setProperty("ORDER", 2)
      graph.node(1000124).setProperty("ARGUMENT_INDEX", 2)
      graph.node(1000124).setProperty("CODE", "printf(\"What is the meaning of life?\\n\")")
      graph.node(1000124).setProperty("COLUMN_NUMBER", 2)
      graph.node(1000124).setProperty("METHOD_FULL_NAME", "printf")
      graph.node(1000124).setProperty("TYPE_FULL_NAME", "ANY")
      graph.node(1000124).setProperty("LINE_NUMBER", 10)
      graph.node(1000124).setProperty("DISPATCH_TYPE", "STATIC_DISPATCH")
      graph.node(1000124).setProperty("SIGNATURE", "TODO assignment signature")
      graph.node(1000124).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
      graph.node(1000124).setProperty("NAME", "printf")

      graph.node(1000125).setProperty("ORDER", 1)
      graph.node(1000125).setProperty("ARGUMENT_INDEX", 1)
      graph.node(1000125).setProperty("CODE", "\"What is the meaning of life?\\n\"")
      graph.node(1000125).setProperty("COLUMN_NUMBER", 9)
      graph.node(1000125).setProperty("TYPE_FULL_NAME", "char *")
      graph.node(1000125).setProperty("LINE_NUMBER", 10)
      graph.node(1000125).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())

      graph.node(1000126).setProperty("ORDER", 3)
      graph.node(1000126).setProperty("ARGUMENT_INDEX", 3)
      graph.node(1000126).setProperty("CODE", "exit(0)")
      graph.node(1000126).setProperty("COLUMN_NUMBER", 2)
      graph.node(1000126).setProperty("METHOD_FULL_NAME", "exit")
      graph.node(1000126).setProperty("TYPE_FULL_NAME", "ANY")
      graph.node(1000126).setProperty("LINE_NUMBER", 11)
      graph.node(1000126).setProperty("DISPATCH_TYPE", "STATIC_DISPATCH")
      graph.node(1000126).setProperty("SIGNATURE", "TODO assignment signature")
      graph.node(1000126).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
      graph.node(1000126).setProperty("NAME", "exit")

      graph.node(1000127).setProperty("ORDER", 1)
      graph.node(1000127).setProperty("ARGUMENT_INDEX", 1)
      graph.node(1000127).setProperty("CODE", "0")
      graph.node(1000127).setProperty("COLUMN_NUMBER", 7)
      graph.node(1000127).setProperty("TYPE_FULL_NAME", "int")
      graph.node(1000127).setProperty("LINE_NUMBER", 11)
      graph.node(1000127).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())

      graph.node(1000128).setProperty("ORDER", 4)
      graph.node(1000128).setProperty("CODE", "RET")
      graph.node(1000128).setProperty("COLUMN_NUMBER", 0)
      graph.node(1000128).setProperty("LINE_NUMBER", 5)
      graph.node(1000128).setProperty("TYPE_FULL_NAME", "int")
      graph.node(1000128).setProperty("EVALUATION_STRATEGY", "BY_VALUE")
      graph.node(1000128).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())

      graph.node(1000100).addEdge("AST", graph.node(1000101))
      graph.node(1000101).addEdge("AST", graph.node(1000102)) // buggy edge (does not get removed when one of its nodes gets removed)
      graph.node(1000102).addEdge("AST", graph.node(1000103))
      graph.node(1000102).addEdge("AST", graph.node(1000104))
      graph.node(1000102).addEdge("AST", graph.node(1000105))
      graph.node(1000102).addEdge("AST", graph.node(1000128))
      graph.node(1000105).addEdge("AST", graph.node(1000106))
      graph.node(1000105).addEdge("AST", graph.node(1000124))
      graph.node(1000105).addEdge("AST", graph.node(1000126))
      graph.node(1000106).addEdge("CONDITION", graph.node(1000107))
      graph.node(1000106).addEdge("AST", graph.node(1000107))
      graph.node(1000106).addEdge("AST", graph.node(1000118))
      graph.node(1000107).addEdge("ARGUMENT", graph.node(1000108))
      graph.node(1000107).addEdge("ARGUMENT", graph.node(1000111))
      graph.node(1000107).addEdge("AST", graph.node(1000108))
      graph.node(1000107).addEdge("AST", graph.node(1000111))
      graph.node(1000108).addEdge("ARGUMENT", graph.node(1000109))
      graph.node(1000108).addEdge("ARGUMENT", graph.node(1000110))
      graph.node(1000108).addEdge("AST", graph.node(1000109))
      graph.node(1000108).addEdge("AST", graph.node(1000110))
      graph.node(1000109).addEdge("REF", graph.node(1000103))
      graph.node(1000111).addEdge("ARGUMENT", graph.node(1000112))
      graph.node(1000111).addEdge("ARGUMENT", graph.node(1000117))
      graph.node(1000111).addEdge("AST", graph.node(1000112))
      graph.node(1000111).addEdge("AST", graph.node(1000117))
      graph.node(1000112).addEdge("ARGUMENT", graph.node(1000113))
      graph.node(1000112).addEdge("ARGUMENT", graph.node(1000116))
      graph.node(1000112).addEdge("AST", graph.node(1000113))
      graph.node(1000112).addEdge("AST", graph.node(1000116))
      graph.node(1000113).addEdge("ARGUMENT", graph.node(1000114))
      graph.node(1000113).addEdge("ARGUMENT", graph.node(1000115))
      graph.node(1000113).addEdge("AST", graph.node(1000114))
      graph.node(1000113).addEdge("AST", graph.node(1000115))
      graph.node(1000114).addEdge("REF", graph.node(1000104))
      graph.node(1000118).addEdge("AST", graph.node(1000119))
      graph.node(1000118).addEdge("AST", graph.node(1000122))
      graph.node(1000119).addEdge("ARGUMENT", graph.node(1000120))
      graph.node(1000119).addEdge("ARGUMENT", graph.node(1000121))
      graph.node(1000119).addEdge("AST", graph.node(1000120))
      graph.node(1000119).addEdge("AST", graph.node(1000121))
      graph.node(1000122).addEdge("ARGUMENT", graph.node(1000123))
      graph.node(1000122).addEdge("AST", graph.node(1000123))
      graph.node(1000124).addEdge("ARGUMENT", graph.node(1000125))
      graph.node(1000124).addEdge("AST", graph.node(1000125))
      graph.node(1000126).addEdge("ARGUMENT", graph.node(1000127))
      graph.node(1000126).addEdge("AST", graph.node(1000127))
      //printNodes(graph)
      //printEdges(graph)
  */
    }
    printNodes(graph)
    printEdges(graph)

    val usedTypes = collectUsedTypes(graph)

    new CfgCreationPass(cpg, functionKeyPools.last).createAndApply() // MARK
    new StubRemovalPass(cpg).createAndApply()
    new TypeNodePass(/*astCreator.global.usedTypes.keys().asScala.toList*/ usedTypes, cpg, Some(typesKeyPool)).createAndApply()

    cpg
  }

  def collectUsedTypes(graph: Graph): List[String] = {
    var usedTypes = List[String]()

    val itr = graph.nodes()
    while(itr.hasNext) {
      val node = itr.next()
      if(node.propertyMap().containsKey("TYPE_FULL_NAME")) {
        val usedType = node.propertyMap().get("TYPE_FULL_NAME")
        if(!usedTypes.contains(usedType)) {
          usedTypes = usedTypes.appended(usedType.asInstanceOf[String])
        }
      }
    }
    usedTypes
  }

  /**
    * Create an empty CPG, backed by the file at `optionalOutputPath` or
    * in-memory if `optionalOutputPath` is empty.
    * */
  private def initCpg(optionalOutputPath: Option[String]): Cpg = {
    val odbConfig = optionalOutputPath
      .map { outputPath =>
        val outFile = File(outputPath)
        if (outputPath != "" && outFile.exists) {
          logger.info("Output file exists, removing: " + outputPath)
          outFile.delete()
        }
        Config.withDefaults.withStorageLocation(outputPath)
      }
      .getOrElse {
        Config.withDefaults()
      }

    val graph = Graph.open(odbConfig,
                           io.shiftleft.codepropertygraph.generated.nodes.Factories.allAsJava,
                           io.shiftleft.codepropertygraph.generated.edges.Factories.allAsJava)
    new Cpg(graph)
  }

}

object FuzzyC2Cpg {

  private val logger = LoggerFactory.getLogger(classOf[FuzzyC2Cpg])

  def main(args: Array[String]): Unit = {
    parseConfig(args) match {
      case Some(config) =>
        try {
          val fuzzyc = new FuzzyC2Cpg()

          if (config.usePreprocessor) {
            fuzzyc.runWithPreprocessorAndOutput(
              config.inputPaths,
              config.sourceFileExtensions,
              config.includeFiles,
              config.includePaths,
              config.defines,
              config.undefines,
              config.preprocessorExecutable,
              Some(config.outputPath)
            )
          } else {
            println("!!!!!!!!!!!iamhereinelse")
            val cpg = fuzzyc.runAndOutput(config.inputPaths, config.sourceFileExtensions, Some(config.outputPath))
            cpg.close()
            println("cpg closed")
          }

        } catch {
          case NonFatal(ex) =>
            logger.error("Failed to generate CPG.", ex)
            System.exit(1)
        }
      case _ =>
        System.exit(1)
    }
    println("exiting main")
  }

  final case class Config(inputPaths: Set[String] = Set.empty,
                          outputPath: String = "cpg.bin.zip",
                          sourceFileExtensions: Set[String] = Set(".c", ".cc", ".cpp", ".h", ".hpp"),
                          includeFiles: Set[String] = Set.empty,
                          includePaths: Set[String] = Set.empty,
                          defines: Set[String] = Set.empty,
                          undefines: Set[String] = Set.empty,
                          preprocessorExecutable: String = "./fuzzypp/bin/fuzzyppcli",
                          overflowDb: Boolean = false) {
    lazy val usePreprocessor: Boolean =
      includeFiles.nonEmpty || includePaths.nonEmpty || defines.nonEmpty || undefines.nonEmpty
  }

  def parseConfig(args: Array[String]): Option[Config] =
    new scopt.OptionParser[Config](classOf[FuzzyC2Cpg].getSimpleName) {
      arg[String]("<input-dir>")
        .unbounded()
        .text("source directories containing C/C++ code")
        .action((x, c) => c.copy(inputPaths = c.inputPaths + x))
      opt[String]("out")
        .text("(DEPRECATED use `output`) output filename")
        .action { (x, c) =>
          logger.warn("`--out` is DEPRECATED. Use `--output` instead")
          c.copy(outputPath = x)
        }
      opt[String]("output")
        .abbr("o")
        .text("output filename")
        .action((x, c) => c.copy(outputPath = x))
      opt[String]("source-file-ext")
        .unbounded()
        .text("source file extensions to include when gathering source files. Defaults are .c, .cc, .cpp, .h and .hpp")
        .action((pat, cfg) => cfg.copy(sourceFileExtensions = cfg.sourceFileExtensions + pat))
      opt[String]("include")
        .unbounded()
        .text("header include files")
        .action((incl, cfg) => cfg.copy(includeFiles = cfg.includeFiles + incl))
      opt[String]('I', "")
        .unbounded()
        .text("header include paths")
        .action((incl, cfg) => cfg.copy(includePaths = cfg.includePaths + incl))
      opt[String]('D', "define")
        .unbounded()
        .text("define a name")
        .action((d, cfg) => cfg.copy(defines = cfg.defines + d))
      opt[String]('U', "undefine")
        .unbounded()
        .text("undefine a name")
        .action((u, cfg) => cfg.copy(undefines = cfg.undefines + u))
      opt[String]("preprocessor-executable")
        .text("path to the preprocessor executable")
        .action((s, cfg) => cfg.copy(preprocessorExecutable = s))
      help("help").text("display this help message")
      opt[Unit]("overflowdb")
        .text("create overflowdb")
        .action((_, cfg) => cfg.copy(overflowDb = true))
    }.parse(args, Config())

}
