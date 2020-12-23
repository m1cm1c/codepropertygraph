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
import scala.sys.env
import scala.util.control.NonFatal

case class Global(usedTypes: ConcurrentHashMap[String, Boolean] = new ConcurrentHashMap[String, Boolean]())

class FuzzyC2Cpg() {
  import FuzzyC2Cpg.logger
  val REAL_BASE_ID = 1000200l

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

  // Enums do not contain members in the CPG AST. However, this seems useful. So I'm
  // using pretty much the same function I wrote for handling structs (slight modifications).
  def registerStructOrEnum(graph: Graph, wrappedStruct: JsonAST.JValue): Unit = {
    val structId = getFieldInt(wrappedStruct, "id")
    val structAttributesWrapped = getFieldWrapped(wrappedStruct, "attributes")

    val structName = getFieldString(structAttributesWrapped, "name")

    val BASE_ID = REAL_BASE_ID

    graph.addNode(BASE_ID + structId, "TYPE_DECL")
    graph.node(BASE_ID + structId).setProperty("AST_PARENT_TYPE", "") // I'm leaving these two empty because (contrary to the documentation)
    graph.node(BASE_ID + structId).setProperty("AST_PARENT_FULL_NAME", "") // they always seem to be left empty.
    graph.node(BASE_ID + structId).setProperty("ORDER", -1)
    graph.node(BASE_ID + structId).setProperty("INHERITS_FROM_TYPE_FULL_NAME", List())
    graph.node(BASE_ID + structId).setProperty("FULL_NAME", structName) // Could be set to attribute "canonicalName" but in the CPG AST, name and full name always seem to be the same, so ...
    graph.node(BASE_ID + structId).setProperty("IS_EXTERNAL", false)
    graph.node(BASE_ID + structId).setProperty("FILENAME", "")
    graph.node(BASE_ID + structId).setProperty("NAME", structName)

    graph.node(1000101).addEdge("AST", graph.node(BASE_ID + structId))

    val memberComponentsWrapped = getFieldWrapped(wrappedStruct, "children")
    val memberComponents = getFieldList(wrappedStruct, "children").asInstanceOf[List[Map[String, Object]]]

    // Deal with struct members.
    for(memberComponent <- memberComponents) {
      val attributes = memberComponent("attributes").asInstanceOf[Map[String, Object]]
      val memberId = memberComponent("id").toString.toInt
      val nodeName = memberComponent("name").toString
      require(nodeName.equals("VariableDeclaration") || nodeName.equals("EnumValue"))

      val memberName = attributes("name").toString
      val memberType = if(attributes.keys.exists(_.equals("type"))) attributes("type").toString else "ENUM"

      graph.addNode(BASE_ID + memberId, "MEMBER")
      graph.node(BASE_ID + memberId).setProperty("TYPE_FULL_NAME", memberType)
      graph.node(BASE_ID + memberId).setProperty("ORDER", -1)
      graph.node(BASE_ID + memberId).setProperty("CODE", memberName)
      graph.node(BASE_ID + memberId).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
      graph.node(BASE_ID + memberId).setProperty("NAME", memberName)

      graph.node(BASE_ID + structId).addEdge("AST", graph.node(BASE_ID + memberId))
    }
  }

  def registerFunctionHeader(graph: Graph, wrappedFunction: JsonAST.JValue, BASE_ID: Long = REAL_BASE_ID, functionNamePostfix: String = ""): Unit = {
    val functionId = getFieldInt(wrappedFunction, "id")
    val functionAttributesWrapped = getFieldWrapped(wrappedFunction, "attributes")

    val functionName = getFieldString(functionAttributesWrapped, "name") + functionNamePostfix
    val isImplemented = getFieldBoolean(functionAttributesWrapped, "implemented")

    // Ignore unimplemented functions.
    if(!isImplemented) {
      return
    }

    graph.addNode(BASE_ID + functionId, "METHOD")
    graph.node(BASE_ID + functionId).setProperty("COLUMN_NUMBER", 0)
    graph.node(BASE_ID + functionId).setProperty("LINE_NUMBER", 0)
    graph.node(BASE_ID + functionId).setProperty("COLUMN_NUMBER_END", 0)
    graph.node(BASE_ID + functionId).setProperty("IS_EXTERNAL", false)
    graph.node(BASE_ID + functionId).setProperty("SIGNATURE", functionName)
    graph.node(BASE_ID + functionId).setProperty("NAME", functionName)
    graph.node(BASE_ID + functionId).setProperty("AST_PARENT_TYPE", "") // I'm leaving these two empty because (contrary to the documentation)
    graph.node(BASE_ID + functionId).setProperty("AST_PARENT_FULL_NAME", "") // they always seem to be left empty.
    graph.node(BASE_ID + functionId).setProperty("ORDER", -1)
    graph.node(BASE_ID + functionId).setProperty("CODE", functionName)
    graph.node(BASE_ID + functionId).setProperty("FULL_NAME", functionName)
    graph.node(BASE_ID + functionId).setProperty("LINE_NUMBER_END", 0)
    graph.node(BASE_ID + functionId).setProperty("FILENAME", "")

    graph.node(1000101).addEdge("AST", graph.node(BASE_ID + functionId))

    val functionComponentsWrapped = getFieldWrapped(wrappedFunction, "children")
    val functionComponents = getFieldList(wrappedFunction, "children")
    var offset = 0
    val includesDocumentation = functionComponents(0).asInstanceOf[Map[String, Object]]("name").toString.equals("StructuredDocumentation")
    if(includesDocumentation)
      offset += 1
    val includesOverrideSpecifier = functionComponents(offset).asInstanceOf[Map[String, Object]]("name").toString.equals("OverrideSpecifier")
    if(includesOverrideSpecifier)
      offset += 1
    val parameterListComponent = functionComponentsWrapped.children(offset)
    val returnValuesListComponent = functionComponentsWrapped.children(offset + 1)
    // Deal with function parameters.
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

    // Deal with function return values.
    order += 1
    val returnValuesList = returnValuesListComponent.values.asInstanceOf[Map[String, List[Object]]]
    for(attributeSpecificObject <- returnValuesList("children")) {
      val attributeSpecificMap = attributeSpecificObject.asInstanceOf[Map[String, Object]]
      val returnValueId = attributeSpecificMap("id").toString.toInt
      val attributeMap = attributeSpecificMap("attributes").asInstanceOf[Map[String, Object]]
      val returnValueName = attributeMap("name").toString
      val returnValueType = attributeMap("type").toString

      graph.addNode(BASE_ID + returnValueId, "METHOD_RETURN")
      graph.node(BASE_ID + returnValueId).setProperty("ORDER", order)
      graph.node(BASE_ID + returnValueId).setProperty("CODE", returnValueType + " " + returnValueName)
      graph.node(BASE_ID + returnValueId).setProperty("COLUMN_NUMBER", 0)
      graph.node(BASE_ID + returnValueId).setProperty("LINE_NUMBER", 0)
      graph.node(BASE_ID + returnValueId).setProperty("TYPE_FULL_NAME", returnValueType)
      graph.node(BASE_ID + returnValueId).setProperty("EVALUATION_STRATEGY", "BY_VALUE")
      graph.node(BASE_ID + returnValueId).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List()) // Is not part of the original CPG AST for some reason. But including it doesn't seem to break anything, so I included it so it's more similar to other kinds of nodes.
      graph.node(BASE_ID + returnValueId).setProperty("NAME", returnValueName) // Is not part of the original CPG AST because in C, return values cannot be named.

      graph.node(BASE_ID + functionId).addEdge("AST", graph.node(BASE_ID + returnValueId))

      order += 1
    }
  }

  def registerFunctionBody(graph: Graph, modifierDefinitions: List[Map[String, Object]], wrappedFunction: JsonAST.JValue, numberOfModifiersRemoved: Int = 0): Unit = {
    val functionId = getFieldInt(wrappedFunction, "id")
    val functionAttributesWrapped = getFieldWrapped(wrappedFunction, "attributes")

    val functionName = getFieldString(functionAttributesWrapped, "name")
    val isImplemented = getFieldBoolean(functionAttributesWrapped, "implemented")

    // Ignore unimplemented functions.
    if(!isImplemented) {
      return
    }

    val functionComponentsWrapped = getFieldWrapped(wrappedFunction, "children")
    val functionComponents = getFieldList(wrappedFunction, "children")

    var offset = 0
    val includesDocumentation = functionComponents(0).asInstanceOf[Map[String, Object]]("name").toString.equals("StructuredDocumentation")
    if(includesDocumentation)
      offset += 1
    val includesOverrideSpecifier = functionComponents(offset).asInstanceOf[Map[String, Object]]("name").toString.equals("OverrideSpecifier")
    if(includesOverrideSpecifier)
      offset += 1

    val bodyComponent = functionComponents(functionComponents.length-1)
    var modifierComponents = functionComponents.slice(offset + 2, functionComponents.length-1)

    // Remove modifiers that were already dealt with in previous calls to this function.
    modifierComponents = modifierComponents.slice(0, modifierComponents.length - numberOfModifiersRemoved)

    // At this point (after execution of registerFunctionHeader()), only the
    // input parameters and the return value are outgoing AST edges. So the
    // block's order is the same as the number of outgoing edges. The return
    // value's order is one larger than the block's order.
    var numberOfOutgoingAstEdges = 0
    graph.node(REAL_BASE_ID + functionId).out("AST").forEachRemaining(node => numberOfOutgoingAstEdges += 1)
    val blockOrder = numberOfOutgoingAstEdges

    val order = if(numberOfModifiersRemoved == 0) blockOrder else 1

    var blockNodeId = 0l

    // Modifiers of constructors (empty function name) call the parent's
    // constructor. This is not supported.
    if(modifierComponents.length == 0 || functionName.equals("")) {
      // Deal with function body.
      val placeholderReplacement = ""
      val placeholderArguments = List()
      val blockId = registerBlock(graph, bodyComponent.asInstanceOf[Map[String, Object]], order, REAL_BASE_ID, placeholderReplacement, placeholderArguments)
      blockNodeId = REAL_BASE_ID + blockId
    } else {
      // Iterate through modifiers in reverse order because they are nested around
      // the function body with the first modifier forming the outer-most layer.
      // General idea: Pass a "function pointer" to the modifier. In places where
      // the underscore operator occurs, the "function pointer" is used to call
      // the "function". It's not a real function because we cannot use this
      // function (otherwise we couldn't pass function parameters to modifiers)
      // but we can use the bodyBlockId.
      val BASE_ID = 10*(10*functionId+numberOfModifiersRemoved)*REAL_BASE_ID+REAL_BASE_ID

      val subFunctionNamePostfix = "_MODIFIERS_REMOVED_" + (numberOfModifiersRemoved + 1)
      val subFunctionName = functionName + subFunctionNamePostfix
      registerFunctionHeader(graph, wrappedFunction, BASE_ID, subFunctionNamePostfix)
      registerFunctionBody(graph, modifierDefinitions, wrappedFunction, numberOfModifiersRemoved+1)

      val modifierComponent = modifierComponents(modifierComponents.length - 1)
      val modifierInstanceName = registerModifierInstance(graph, modifierDefinitions, BASE_ID, subFunctionName, numberOfModifiersRemoved, modifierComponent.asInstanceOf[Map[String, Object]])

      graph.addNode(BASE_ID - 1, "BLOCK")
      graph.node(BASE_ID - 1).setProperty("ORDER", order)
      graph.node(BASE_ID - 1).setProperty("ARGUMENT_INDEX", order)
      graph.node(BASE_ID - 1).setProperty("CODE", "")
      graph.node(BASE_ID - 1).setProperty("COLUMN_NUMBER", 0)
      graph.node(BASE_ID - 1).setProperty("TYPE_FULL_NAME", "void")
      graph.node(BASE_ID - 1).setProperty("LINE_NUMBER", 0)
      graph.node(BASE_ID - 1).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())

      graph.addNode(BASE_ID, "CALL")
      graph.node(BASE_ID).setProperty("ORDER", 1)
      graph.node(BASE_ID).setProperty("ARGUMENT_INDEX", 1)
      graph.node(BASE_ID).setProperty("CODE", "")
      graph.node(BASE_ID).setProperty("COLUMN_NUMBER", 0)
      graph.node(BASE_ID).setProperty("METHOD_FULL_NAME", modifierInstanceName) // This could alternatively be set to the value of property "FULL_NAME" of node BASE_ID + functionReferencedId.
      graph.node(BASE_ID).setProperty("TYPE_FULL_NAME", "ANY")
      graph.node(BASE_ID).setProperty("LINE_NUMBER", 0)
      graph.node(BASE_ID).setProperty("DISPATCH_TYPE", "STATIC_DISPATCH")
      graph.node(BASE_ID).setProperty("SIGNATURE", "TODO assignment signature")
      graph.node(BASE_ID).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
      graph.node(BASE_ID).setProperty("NAME", modifierInstanceName)

      graph.node(BASE_ID - 1).addEdge("AST", graph.node(BASE_ID))

      blockNodeId = BASE_ID - 1
    }

    // In the outer-most case, an additional AST edge is needed to connect the function definition with the block ID.
    if(numberOfModifiersRemoved == 0) {
      graph.node(REAL_BASE_ID + functionId).addEdge("AST", graph.node(blockNodeId))
    }
  }

  def registerModifierInstance(graph: Graph, modifierDefinitions: List[Map[String, Object]], BASE_ID: Long, placeholderReplacement: String, numberOfModifiersRemoved: Int, modifierInvocation: Map[String, Object]): String = {
    val modifierInvocationChildren = modifierInvocation("children").asInstanceOf[List[Map[String, Object]]]
    val modifierInvocationArguments = modifierInvocationChildren.slice(1, modifierInvocationChildren.length)
    val modifierReferenceId = modifierInvocationChildren(0)("attributes").asInstanceOf[Map[String, Object]]("referencedDeclaration").toString.toInt

    val modifierDefinition = modifierDefinitions.filter(_("id").toString.toInt == modifierReferenceId)(0)

    val modifierName = modifierDefinition("attributes").asInstanceOf[Map[String, Object]]("name").toString
    val modifierInstanceName = modifierName + "_CALLING_" + placeholderReplacement
    val modifierId = modifierDefinition("id").toString.toInt
    val modifierChildren = modifierDefinition("children").asInstanceOf[List[Map[String, Object]]]

    graph.addNode(BASE_ID + modifierId, "METHOD")
    graph.node(BASE_ID + modifierId).setProperty("COLUMN_NUMBER", 0)
    graph.node(BASE_ID + modifierId).setProperty("LINE_NUMBER", 0)
    graph.node(BASE_ID + modifierId).setProperty("COLUMN_NUMBER_END", 0)
    graph.node(BASE_ID + modifierId).setProperty("IS_EXTERNAL", false)
    graph.node(BASE_ID + modifierId).setProperty("SIGNATURE", modifierInstanceName)
    graph.node(BASE_ID + modifierId).setProperty("NAME", modifierInstanceName)
    graph.node(BASE_ID + modifierId).setProperty("AST_PARENT_TYPE", "") // I'm leaving these two empty because (contrary to the documentation)
    graph.node(BASE_ID + modifierId).setProperty("AST_PARENT_FULL_NAME", "") // they always seem to be left empty.
    graph.node(BASE_ID + modifierId).setProperty("ORDER", -1)
    graph.node(BASE_ID + modifierId).setProperty("CODE", modifierInstanceName)
    graph.node(BASE_ID + modifierId).setProperty("FULL_NAME", modifierInstanceName)
    graph.node(BASE_ID + modifierId).setProperty("LINE_NUMBER_END", 0)
    graph.node(BASE_ID + modifierId).setProperty("FILENAME", "")

    graph.node(1000101).addEdge("AST", graph.node(BASE_ID + modifierId))

    var offset = 0
    if(modifierChildren(0)("name").toString.equals("StructuredDocumentation"))
      offset += 1

    val parameterList = modifierChildren(offset+0).asInstanceOf[Map[String, List[Object]]]
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

      graph.node(BASE_ID + modifierId).addEdge("AST", graph.node(BASE_ID + parameterId))

      order += 1
    }

    registerBlock(graph, modifierChildren(offset+1), 1, BASE_ID, placeholderReplacement, modifierInvocationArguments)

    // TODO: IS A RETURN VALUE REQUIRED?

    modifierInstanceName
  }

  def registerBlock(graph: Graph, block: Map[String, Object], order: Int, BASE_ID: Long, placeholderReplacement: String, placeholderArguments: List[Map[String, Object]]): Int = {
    println(block("name"))
    require(block("name").asInstanceOf[String].equals("Block"))

    val blockId = block("id").toString.toInt
    println("block id:")
    println(blockId)
    graph.addNode(BASE_ID + blockId, "BLOCK")
    graph.node(BASE_ID + blockId).setProperty("ORDER", order)
    graph.node(BASE_ID + blockId).setProperty("ARGUMENT_INDEX", order)
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
    var statementOrder = 1
    for(statement <- statementsList) {
      val statementIds = registerStatement(graph, statement, statementOrder, BASE_ID, placeholderReplacement, placeholderArguments)
      for(statementId <- statementIds) {
        graph.node(BASE_ID + blockId).addEdge("AST", graph.node(BASE_ID + statementId))
      }
      statementOrder += statementIds.length
    }
    println(statementsList.length)

    blockId
  }

  def registerStatement(graph: Graph, statement: Object, _order: Int, BASE_ID: Long, placeholderReplacement: String, placeholderArguments: List[Map[String, Object]]): Array[Long] = {
    // Avoiding stupid Scala rule about parameters being read-only.
    var order = _order

    val statementMap = statement.asInstanceOf[Map[String, Object]]
    println(statementMap)
    val statementName = statementMap("name").toString
    println("Statement name: " + statementName)
    val statementId = statementMap("id").toString.toInt
    println("Statement ID: " + statementId)

    if(statementName.equals("EmitStatement")) {
      return Array()
    }

    if(statementName.equals("PlaceholderStatement")) {
      graph.addNode(BASE_ID + statementId, "CALL")
      graph.node(BASE_ID + statementId).setProperty("ORDER", order)
      graph.node(BASE_ID + statementId).setProperty("ARGUMENT_INDEX", order)
      graph.node(BASE_ID + statementId).setProperty("CODE", placeholderReplacement + "(...)")
      graph.node(BASE_ID + statementId).setProperty("COLUMN_NUMBER", 0)
      graph.node(BASE_ID + statementId).setProperty("METHOD_FULL_NAME", placeholderReplacement)
      graph.node(BASE_ID + statementId).setProperty("TYPE_FULL_NAME", "ANY")
      graph.node(BASE_ID + statementId).setProperty("LINE_NUMBER", 0)
      graph.node(BASE_ID + statementId).setProperty("DISPATCH_TYPE", "STATIC_DISPATCH")
      graph.node(BASE_ID + statementId).setProperty("SIGNATURE", "TODO assignment signature")
      graph.node(BASE_ID + statementId).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
      graph.node(BASE_ID + statementId).setProperty("NAME", placeholderReplacement)

      var argumentNumber = 1
      for(argumentComponent <- placeholderArguments) {
        val argumentId = registerStatement(graph, argumentComponent, argumentNumber, BASE_ID, placeholderReplacement, placeholderArguments)(0)
        graph.node(BASE_ID + statementId).addEdge("ARGUMENT", graph.node(BASE_ID + argumentId))
        graph.node(BASE_ID + statementId).addEdge("AST", graph.node(BASE_ID + argumentId))
        argumentNumber += 1
      }

      return Array(statementId)
    }

    if(statementName.equals("Literal") || statementName.equals("Identifier")) {
      val statementAttributes = statementMap("attributes").asInstanceOf[Map[String, Object]]
      graph.addNode(BASE_ID + statementId, (if (statementName.equals("Identifier")) "IDENTIFIER" else "LITERAL"))
      graph.node(BASE_ID + statementId).setProperty("ORDER", order)
      graph.node(BASE_ID + statementId).setProperty("ARGUMENT_INDEX", order)
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

    if(statementName.equals("Return")) {
      /*
      // Getting some code here isn't easy. We need to try a few options.
      val variableAttributes = statementChildren(0)("attributes").asInstanceOf[Map[String, Object]]
      val symbol = if(variableAttributes.keys.exists(_ == "value")) {
        variableAttributes("value").toString
      } else {
        val functionCallAttributes = statementChildren(0)("children").asInstanceOf[List[Map[String, Object]]](0)("attributes").asInstanceOf[Map[String, Object]]
        functionCallAttributes("value") + "(...)"
      }
      val code = "return " + symbol
      println(code)
       */
      val code = "return (...)"
      graph.addNode(BASE_ID + statementId, "RETURN")
      graph.node(BASE_ID + statementId).setProperty("ORDER", order)
      graph.node(BASE_ID + statementId).setProperty("LINE_NUMBER", 0)
      graph.node(BASE_ID + statementId).setProperty("ARGUMENT_INDEX", order)
      graph.node(BASE_ID + statementId).setProperty("CODE", code)
      graph.node(BASE_ID + statementId).setProperty("COLUMN_NUMBER", 0)

      // The shared statementChildren variable definition cannot be used for return
      // statements because return statements don't always have children.
      if(statementMap.keys.exists(_.equals("children"))) {
        val statementChildren = statementMap("children").asInstanceOf[List[Map[String, Object]]]
        println("Number of statement children: " + statementChildren.length)

        val idChild = registerStatement(graph, statementChildren(0), 1, BASE_ID, placeholderReplacement, placeholderArguments)(0)

        graph.node(BASE_ID + statementId).addEdge("ARGUMENT", graph.node(BASE_ID + idChild))
        graph.node(BASE_ID + statementId).addEdge("AST", graph.node(BASE_ID + idChild))
      }

      return Array(statementId)
    }

    val statementChildren = statementMap("children").asInstanceOf[List[Map[String, Object]]]
    println("Number of statement children: " + statementChildren.length)

    // The CPG AST does not seem to know about tuple expressions,
    // so their children get passed right through.
    if(statementName.equals("TupleExpression")) {
      println("Processing tuple expression")

      var statementIds = List[Long]()
      for(statementChild <- statementChildren) {
        val innerStatementIds = registerStatement(graph, statementChild, order, BASE_ID, placeholderReplacement, placeholderArguments)
        statementIds = statementIds.concat(innerStatementIds)
      }

      return statementIds.toArray
    }

    if(statementName.equals("MemberAccess")) {
      val memberAccessId = memberAccessHelper(graph, BASE_ID, statement.asInstanceOf[Map[String, Object]], placeholderReplacement, placeholderArguments)
      return Array(memberAccessId)
    }

    if(!statementName.equals("ExpressionStatement") && !statementName.equals("Block")
      && !statementName.equals("IfStatement") && !statementName.equals("Conditional")
      && !statementName.equals("WhileStatement")
      && !statementName.equals("DoWhileStatement") && !statementName.equals("ForStatement")
      && !statementName.equals("BinaryOperation") && !statementName.equals("UnaryOperation")
      && !statementName.equals("FunctionCall") && !statementName.equals("VariableDeclarationStatement")
      && !statementName.equals("IndexAccess")) {
      println("panic!!! unknown statement with statement name: " + statementName)
      return Array()
    }

    if(statementName.equals("Block")) {
      val blockId = registerBlock(graph, statementMap, order, BASE_ID, placeholderReplacement, placeholderArguments)
      return Array(blockId)
    }

    if(statementName.equals("BinaryOperation")) {
      val statementAttributes = statementMap("attributes").asInstanceOf[Map[String, Object]]
      val statementDataType = statementAttributes("type").toString

      val idLeftChild = registerStatement(graph, statementChildren(0), 1, BASE_ID, placeholderReplacement, placeholderArguments)(0)
      val idRightChild = registerStatement(graph, statementChildren(1), 2, BASE_ID, placeholderReplacement, placeholderArguments)(0)

      val codeLeft = graph.node(BASE_ID + idLeftChild).property("CODE")
      val codeRight = graph.node(BASE_ID + idRightChild).property("CODE")
      val code = "(" + codeLeft + ") + (" + codeRight + ")"

      val operatorName = getBinaryOperatorName(statementAttributes("operator").toString)
      graph.addNode(BASE_ID + statementId, "CALL")
      graph.node(BASE_ID + statementId).setProperty("ORDER", order)
      graph.node(BASE_ID + statementId).setProperty("ARGUMENT_INDEX", order)
      graph.node(BASE_ID + statementId).setProperty("CODE", code)
      graph.node(BASE_ID + statementId).setProperty("COLUMN_NUMBER", 0)
      graph.node(BASE_ID + statementId).setProperty("METHOD_FULL_NAME", operatorName)
      graph.node(BASE_ID + statementId).setProperty("TYPE_FULL_NAME", "ANY")
      graph.node(BASE_ID + statementId).setProperty("LINE_NUMBER", 0)
      graph.node(BASE_ID + statementId).setProperty("DISPATCH_TYPE", "STATIC_DISPATCH")
      graph.node(BASE_ID + statementId).setProperty("SIGNATURE", "TODO assignment signature")
      graph.node(BASE_ID + statementId).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
      graph.node(BASE_ID + statementId).setProperty("NAME", operatorName)

      graph.node(BASE_ID + statementId).addEdge("ARGUMENT", graph.node(BASE_ID + idLeftChild))
      graph.node(BASE_ID + statementId).addEdge("ARGUMENT", graph.node(BASE_ID + idRightChild))

      graph.node(BASE_ID + statementId).addEdge("AST", graph.node(BASE_ID + idLeftChild))
      graph.node(BASE_ID + statementId).addEdge("AST", graph.node(BASE_ID + idRightChild))

      return Array(statementId)
    }

    if(statementName.equals("UnaryOperation")) {
      val statementChildren = statementMap("children").asInstanceOf[List[Object]]
      val statementAttributes = statementMap("attributes").asInstanceOf[Map[String, Object]]

      val operatorSymbol = statementAttributes("operator").toString
      val isPrefixOperator = statementAttributes("prefix").equals(true)

      val idChild = registerStatement(graph, statementChildren(0), 1, BASE_ID, placeholderReplacement, placeholderArguments)(0)
      val symbol = graph.node(BASE_ID + idChild).property("CODE")

      val code = if (isPrefixOperator) operatorSymbol + symbol else symbol + operatorSymbol
      val operatorName = getUnaryOperatorName(operatorSymbol, isPrefixOperator)

      graph.addNode(BASE_ID + statementId, "CALL")
      graph.node(BASE_ID + statementId).setProperty("ORDER", order)
      graph.node(BASE_ID + statementId).setProperty("ARGUMENT_INDEX", order)
      graph.node(BASE_ID + statementId).setProperty("CODE", code)
      graph.node(BASE_ID + statementId).setProperty("COLUMN_NUMBER", 0)
      graph.node(BASE_ID + statementId).setProperty("METHOD_FULL_NAME", operatorName)
      graph.node(BASE_ID + statementId).setProperty("TYPE_FULL_NAME", "ANY")
      graph.node(BASE_ID + statementId).setProperty("LINE_NUMBER", 0)
      graph.node(BASE_ID + statementId).setProperty("DISPATCH_TYPE", "STATIC_DISPATCH")
      graph.node(BASE_ID + statementId).setProperty("SIGNATURE", "TODO assignment signature")
      graph.node(BASE_ID + statementId).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
      graph.node(BASE_ID + statementId).setProperty("NAME", operatorName)

      println("my child is:")
      println(graph.node(BASE_ID + idChild))
      graph.node(BASE_ID + statementId).addEdge("ARGUMENT", graph.node(BASE_ID + idChild))
      graph.node(BASE_ID + statementId).addEdge("AST", graph.node(BASE_ID + idChild))

      return Array(statementId)
    }

    if(statementName.equals("VariableDeclarationStatement")) {
      var returnIds = List[Long]()

      // There are 3 cases depending on the number of children:
      // 1 child:    A VariableDeclaration.
      // 2 children: The first child is a VariableDeclaration.
      //             The second child is what that variable is assigned.
      // 3 children: The first n-1 children are VariableDeclarations.
      //             The last child's children are what the variables are assigned.
      require(statementChildren.length > 0)
      if(statementChildren.length == 1) {
        registerVariableDeclaration(statementChildren(0))
      } else if(statementChildren.length == 2) {
        val (variableAttributes, assignmentLeftId, localId) = registerVariableDeclaration(statementChildren(0))
        registerVariableAssignment(variableAttributes, assignmentLeftId, localId, statementChildren(1))
      } else if(statementChildren.length >= 3) {
        val variableDeclarationOperations = statementChildren.slice(0, statementChildren.length-1)
        val statementsRight = statementChildren(statementChildren.length-1)("children").asInstanceOf[List[Map[String, Object]]]
        require(variableDeclarationOperations.length == statementsRight.length)

        for(i <- 0 until statementsRight.length) {
          val (variableAttributes, assignmentLeftId, localId) = registerVariableDeclaration(variableDeclarationOperations(i))
          registerVariableAssignment(variableAttributes, assignmentLeftId, localId, statementsRight(i))
        }
      } else {
        require(false)
      }

      def registerVariableDeclaration(operation: Map[String, Object]): (Map[String, Object], Long, Int) = {
        val variableAttributes = operation("attributes").asInstanceOf[Map[String, Object]]
        val variableDataType = variableAttributes("type").toString
        val variableName = variableAttributes("name").toString

        val declarationOperationId = operation("id").toString.toInt
        require(operation("name").toString.equals("VariableDeclaration"))

        graph.addNode(BASE_ID + declarationOperationId, "LOCAL")
        graph.node(BASE_ID + declarationOperationId).setProperty("TYPE_FULL_NAME", variableDataType)
        graph.node(BASE_ID + declarationOperationId).setProperty("ORDER", order)
        graph.node(BASE_ID + declarationOperationId).setProperty("CODE", variableName)
        graph.node(BASE_ID + declarationOperationId).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
        graph.node(BASE_ID + declarationOperationId).setProperty("NAME", variableName)
        order += 1
        returnIds = returnIds.appended(declarationOperationId)

        (variableAttributes, declarationOperationId + 1 * BASE_ID, declarationOperationId)
      }

      def registerVariableAssignment(variableAttributes: Map[String, Object], assignmentLeftId: Long, localId: Long, statementRight: Map[String, Object]) {
        val variableName = variableAttributes("name").toString

        val statementRightAttributes = statementRight("attributes").asInstanceOf[Map[String, Object]]
        val statementRightId = registerStatement(graph, statementRight, 2, BASE_ID, placeholderReplacement, placeholderArguments)(0)

        // We need more nodes than the Solidity AST provides. Therefore, instead of declarationOperationId, 1*BASE_ID + declarationOperationId is passed in.
        // The reason that we need more nodes is that the CPG AST requires you to link to an Identifier Node which in turn links to the Local node. You cannot link
        // to a Local node directly via an argument edge.
        // Update: Need even more IDs. => 4*BASE_ID + statementRightId
        assignmentHelper(graph, BASE_ID, 4*BASE_ID + statementRightId, order, assignmentLeftId, variableName, getAssignmentOperatorName("="), localId, statementRightId)
        order += 1
        returnIds = returnIds.appended(4*BASE_ID + statementRightId)
      }

      return returnIds.toArray
    }

    val operation = statementChildren(0)
    val operationName = operation("name").toString
    val operationAttributes = operation("attributes").asInstanceOf[Map[String, Object]]

    if(statementName.equals("IfStatement") || statementName.equals("Conditional")
      || statementName.equals("WhileStatement")
      || statementName.equals("DoWhileStatement") || statementName.equals("ForStatement")) {
      graph.addNode(BASE_ID + statementId, "CONTROL_STRUCTURE")
      graph.node(BASE_ID + statementId).setProperty("PARSER_TYPE_NAME", statementName)
      graph.node(BASE_ID + statementId).setProperty("ORDER", order)
      graph.node(BASE_ID + statementId).setProperty("LINE_NUMBER", 0)
      graph.node(BASE_ID + statementId).setProperty("ARGUMENT_INDEX", order)
      graph.node(BASE_ID + statementId).setProperty("CODE", "")
      graph.node(BASE_ID + statementId).setProperty("COLUMN_NUMBER", 0)

      if(statementName.equals("IfStatement") || statementName.equals("Conditional")
        || statementName.equals("WhileStatement") || statementName.equals("DoWhileStatement")) {
        val conditionId = registerStatement(graph, operation, 1, BASE_ID, placeholderReplacement, placeholderArguments)(0)
        // There never are several action IDs. This is because in Solidity,
        // variable delarations in an if's or loop's body is illegal unless that
        // body is a block.
        val actionId = registerStatement(graph, statementChildren(1), 2, BASE_ID, placeholderReplacement, placeholderArguments)(0)

        graph.node(BASE_ID + statementId).addEdge("CONDITION", graph.node(BASE_ID + conditionId))
        graph.node(BASE_ID + statementId).addEdge("AST", graph.node(BASE_ID + conditionId))
        graph.node(BASE_ID + statementId).addEdge("AST", graph.node(BASE_ID + actionId))

        // Handle "else" part if present.
        if(statementChildren.length == 3) {
          val alternativeActionId = registerStatement(graph, statementChildren(2), 1, BASE_ID, placeholderReplacement, placeholderArguments)(0)

          // We need a node that is not present in the Solidity AST so we add the BASE_ID twice.
          graph.addNode(2*BASE_ID + statementId, "CONTROL_STRUCTURE")
          graph.node(2*BASE_ID + statementId).setProperty("PARSER_TYPE_NAME", "ElseStatement")
          graph.node(2*BASE_ID + statementId).setProperty("ORDER", order+1) // This does not need to be propagated outwards. There just are duplicate order numbers if there is a subsequent statement. I have no idea why.
          graph.node(2*BASE_ID + statementId).setProperty("LINE_NUMBER", 0)
          graph.node(2*BASE_ID + statementId).setProperty("ARGUMENT_INDEX", order+1)
          graph.node(2*BASE_ID + statementId).setProperty("CODE", "else")
          graph.node(2*BASE_ID + statementId).setProperty("COLUMN_NUMBER", 0)

          graph.node(BASE_ID + statementId).addEdge("AST", graph.node(2*BASE_ID + statementId))
          graph.node(2*BASE_ID + statementId).addEdge("AST", graph.node(BASE_ID + alternativeActionId))
        }
      } else {
        val initialActionIds = registerStatement(graph, operation, 1, BASE_ID, placeholderReplacement, placeholderArguments)
        val conditionId = registerStatement(graph, statementChildren(1), 2, BASE_ID, placeholderReplacement, placeholderArguments)(0)
        val incrementId = registerStatement(graph, statementChildren(2), 3, BASE_ID, placeholderReplacement, placeholderArguments)(0)
        val actionId = registerStatement(graph, statementChildren(3), 4, BASE_ID, placeholderReplacement, placeholderArguments)(0)

        // Weird order bc that's the order that the CPG AST uses.
        graph.node(BASE_ID + statementId).addEdge("CONDITION", graph.node(BASE_ID + conditionId))
        for(initialActionId <- initialActionIds)
          graph.node(BASE_ID + statementId).addEdge("AST", graph.node(BASE_ID + initialActionId))
        graph.node(BASE_ID + statementId).addEdge("AST", graph.node(BASE_ID + conditionId))
        graph.node(BASE_ID + statementId).addEdge("AST", graph.node(BASE_ID + incrementId))
        graph.node(BASE_ID + statementId).addEdge("AST", graph.node(BASE_ID + actionId))
      }
      return Array(statementId)
    }

    if(statementName.equals("IndexAccess")) {
      val leftId = registerStatement(graph, statementChildren(0), 1, BASE_ID, placeholderReplacement, placeholderArguments)(0)
      val rightId = registerStatement(graph, statementChildren(1), 2, BASE_ID, placeholderReplacement, placeholderArguments)(0)

      val arrayName = graph.node(BASE_ID + leftId).property("CODE").toString
      val indexAccessed = graph.node(BASE_ID + rightId).property("CODE").toString

      val code = arrayName + "[" + indexAccessed + "]"

      graph.addNode(BASE_ID + statementId, "CALL")
      graph.node(BASE_ID + statementId).setProperty("ORDER", order)
      graph.node(BASE_ID + statementId).setProperty("ARGUMENT_INDEX", order)
      graph.node(BASE_ID + statementId).setProperty("CODE", code)
      graph.node(BASE_ID + statementId).setProperty("COLUMN_NUMBER", 0)
      graph.node(BASE_ID + statementId).setProperty("METHOD_FULL_NAME", "<operator>.assignment")
      graph.node(BASE_ID + statementId).setProperty("TYPE_FULL_NAME", "ANY")
      graph.node(BASE_ID + statementId).setProperty("LINE_NUMBER", 0)
      graph.node(BASE_ID + statementId).setProperty("DISPATCH_TYPE", "STATIC_DISPATCH")
      graph.node(BASE_ID + statementId).setProperty("SIGNATURE", "TODO assignment signature")
      graph.node(BASE_ID + statementId).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
      graph.node(BASE_ID + statementId).setProperty("NAME", "<operator>.assignment")
      order += 1

      graph.node(BASE_ID + statementId).addEdge("ARGUMENT", graph.node(BASE_ID + leftId))
      graph.node(BASE_ID + statementId).addEdge("ARGUMENT", graph.node(BASE_ID + rightId))

      graph.node(BASE_ID + statementId).addEdge("AST", graph.node(BASE_ID + leftId))
      graph.node(BASE_ID + statementId).addEdge("AST", graph.node(BASE_ID + rightId))

      return Array(statementId)
    }

    if(statementName.equals("FunctionCall")) {
      val functionComponent = statementChildren(0)
      val argumentComponents = statementChildren.slice(1, statementChildren.length)

      val functionAttributes = {
        if(!functionComponent.keys.exists(_.equals("name")) || !functionComponent("name").equals("NewExpression")) // Regular function call.
          functionComponent("attributes").asInstanceOf[Map[String, Object]]
        else // "new" expression (object creation).
          statementMap("attributes").asInstanceOf[Map[String, Object]]
      }

      val functionName = {
        if(functionAttributes.keys.exists(_.equals("value"))) // Regular function call.
          functionAttributes("value").toString
        else { // "new" expression (object creation).
          val typeName = functionAttributes("type").toString
          "new " + typeName
        }
      }

      // val functionReferencedId = functionAttributes("referencedDeclaration").toString.toInt

      graph.addNode(BASE_ID + statementId, "CALL")
      graph.node(BASE_ID + statementId).setProperty("ORDER", order)
      graph.node(BASE_ID + statementId).setProperty("ARGUMENT_INDEX", order)
      graph.node(BASE_ID + statementId).setProperty("CODE", functionName + "(...)")
      graph.node(BASE_ID + statementId).setProperty("COLUMN_NUMBER", 0)
      graph.node(BASE_ID + statementId).setProperty("METHOD_FULL_NAME", functionName) // This could alternatively be set to the value of property "FULL_NAME" of node BASE_ID + functionReferencedId.
      graph.node(BASE_ID + statementId).setProperty("TYPE_FULL_NAME", "ANY")
      graph.node(BASE_ID + statementId).setProperty("LINE_NUMBER", 0)
      graph.node(BASE_ID + statementId).setProperty("DISPATCH_TYPE", "STATIC_DISPATCH")
      graph.node(BASE_ID + statementId).setProperty("SIGNATURE", "TODO assignment signature")
      graph.node(BASE_ID + statementId).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
      graph.node(BASE_ID + statementId).setProperty("NAME", functionName)

      println(functionComponent)
      println(argumentComponents)

      var argumentNumber = 1
      for(argumentComponent <- argumentComponents) {
        val argumentId = registerStatement(graph, argumentComponent, argumentNumber, BASE_ID, placeholderReplacement, placeholderArguments)(0)
        graph.node(BASE_ID + statementId).addEdge("ARGUMENT", graph.node(BASE_ID + argumentId))
        graph.node(BASE_ID + statementId).addEdge("AST", graph.node(BASE_ID + argumentId))
        argumentNumber += 1
      }

      return Array(statementId)
    }

    statementName match {
      case "ExpressionStatement" => {
        println("Operation name: " + operationName)

        if(operationName.equals("FunctionCall")) {
          return registerStatement(graph, operation, order, BASE_ID, placeholderReplacement, placeholderArguments)
        }

        if(operationName.equals("BinaryOperation")) {
          return registerStatement(graph, operation, order, BASE_ID, placeholderReplacement, placeholderArguments)
        }

        if(operationName.equals("UnaryOperation")) {
          return registerStatement(graph, operation, order, BASE_ID, placeholderReplacement, placeholderArguments)
        }

        if(operationName.equals("Identifier")) {
          return registerStatement(graph, operation, order, BASE_ID, placeholderReplacement, placeholderArguments)
        }

        val operationChildren = operation("children").asInstanceOf[List[Object]]

        if (operationName.equals("Assignment")) {
          println("Handling Assignment")
          val operatorName = getAssignmentOperatorName(operationAttributes("operator").toString)
          require(operationChildren.length == 2)

          var statementIds = List[Long]()
          var statementsLeft = List[Map[String, Object]]()
          var statementsRight = List[Map[String, Object]]()
          var localVariablesIds = List[Long]()

          if (!operationAttributes("type").equals("tuple()")) {
            statementIds = List(statementId)
            statementsLeft = List(operationChildren(0).asInstanceOf[Map[String, Object]])
            statementsRight = List(operationChildren(1).asInstanceOf[Map[String, Object]])
          } else {
            // Create a temporary variable for each value on the right that is
            // then assigned that value.
            statementsRight = operationChildren(1).asInstanceOf[Map[String, List[Map[String, Object]]]]("children")

            var tupleElementNumber = 0
            for (statementRight <- statementsRight) {
              val statementRightId = statementRight("id").toString.toInt
              val variableDataType = statementRight("attributes").asInstanceOf[Map[String, Object]]("type").toString
              val variableName = "tuple_element_" + tupleElementNumber

              graph.addNode(3 * BASE_ID + statementRightId, "LOCAL")
              graph.node(3 * BASE_ID + statementRightId).setProperty("TYPE_FULL_NAME", variableDataType)
              graph.node(3 * BASE_ID + statementRightId).setProperty("ORDER", order)
              graph.node(3 * BASE_ID + statementRightId).setProperty("CODE", variableName)
              graph.node(3 * BASE_ID + statementRightId).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
              graph.node(3 * BASE_ID + statementRightId).setProperty("NAME", variableName)
              order += 1

              // These statements are faked with referenced IDs shifted by 2*BASE_ID such that when
              // BASE_ID is added later on to form the node IDs, the same offset as used above
              // (3*BASE_ID) is reached.
              var statementLeft = Map[String, Object]()
              statementLeft += ("id" -> (4 * BASE_ID + statementRightId).asInstanceOf[Object])
              statementLeft += ("name" -> "Identifier")
              var statementLeftAttributes = Map[String, Object]()
              statementLeftAttributes += ("type" -> variableDataType)
              statementLeftAttributes += ("value" -> variableName)
              val localVariableId = 2 * BASE_ID + statementRightId
              localVariablesIds = localVariablesIds.appended(localVariableId)
              statementLeftAttributes += ("referencedDeclaration" -> localVariableId.asInstanceOf[Object])
              statementLeft += ("attributes" -> statementLeftAttributes)

              statementsLeft = statementsLeft.appended(statementLeft)
              statementIds = statementIds.appended(6 * BASE_ID + statementRightId)

              tupleElementNumber += 1
            }

            // Assign the values of the temporary variables to the variables on the left.
            // There is no need to actually copy these lists because lists are immutable.
            val statementsLeftCopy = statementsLeft
            val statementsRightCopy = statementsRight
            statementsRight = List.concat(statementsRight, statementsLeftCopy.map(statementTmp => {
              val updatedId = statementTmp("id").toString.toInt + 8 * BASE_ID
              statementTmp + ("id" -> updatedId.asInstanceOf[Object])
            }))
            statementsLeft = List.concat(statementsLeft, operationChildren(0).asInstanceOf[Map[String, List[Map[String, Object]]]]("children"))
            statementIds = List.concat(statementIds, statementIds.map(_ + 2 * BASE_ID))
          }

          require(statementIds.length == statementsLeft.length)
          require(statementIds.length == statementsRight.length)

          for (i <- 0 until statementIds.length) {
            val statementIdI = statementIds(i)
            val statementLeft = statementsLeft(i)
            val statementRight = statementsRight(i)

            val statementLeftId = statementLeft("id").toString.toInt
            val statementRightId = registerStatement(graph, statementRight, 2, BASE_ID, placeholderReplacement, placeholderArguments)(0)

            val statementLeftAttributes = statementLeft("attributes").asInstanceOf[Map[String, Object]]
            val statementLeftKind = statementLeft("name").toString

            println(statementIdI + ": " + statementLeftId + " <- " + statementRightId)

            if (statementLeftKind.equals("Identifier")) {
              val statementLeftVariableName = statementLeftAttributes("value").toString
              val statementLeftReferencedId = statementLeftAttributes("referencedDeclaration").toString.toInt
              println("entering assignment helper")
              assignmentHelper(graph, BASE_ID, statementIdI, order, statementLeftId, statementLeftVariableName, operatorName, statementLeftReferencedId, statementRightId)
              order += 1
              println("exited assignment helper")
            } else if (statementLeftKind.equals("MemberAccess")) {
              val memberAccess = statementLeft
              val memberName = statementLeftAttributes("member_name").toString
              val struct = statementLeft("children").asInstanceOf[List[Map[String, Object]]](0)
              val structAttributes = struct("attributes").asInstanceOf[Map[String, Object]]
              val structName = structAttributes("value").toString
              val structId = struct("id").toString.toInt
              val statementLeftVariableName = structName + "." + memberName

              graph.addNode(BASE_ID + statementIdI, "CALL")
              graph.node(BASE_ID + statementIdI).setProperty("ORDER", order)
              graph.node(BASE_ID + statementIdI).setProperty("ARGUMENT_INDEX", order)
              graph.node(BASE_ID + statementIdI).setProperty("CODE", statementLeftVariableName + " = (...)")
              graph.node(BASE_ID + statementIdI).setProperty("COLUMN_NUMBER", 0)
              graph.node(BASE_ID + statementIdI).setProperty("METHOD_FULL_NAME", operatorName)
              graph.node(BASE_ID + statementIdI).setProperty("TYPE_FULL_NAME", "ANY")
              graph.node(BASE_ID + statementIdI).setProperty("LINE_NUMBER", 0)
              graph.node(BASE_ID + statementIdI).setProperty("DISPATCH_TYPE", "STATIC_DISPATCH")
              graph.node(BASE_ID + statementIdI).setProperty("SIGNATURE", "TODO assignment signature")
              graph.node(BASE_ID + statementIdI).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
              graph.node(BASE_ID + statementIdI).setProperty("NAME", operatorName)
              order += 1

              memberAccessHelper(graph, BASE_ID, memberAccess, placeholderReplacement, placeholderArguments)

              graph.node(BASE_ID + statementIdI).addEdge("ARGUMENT", graph.node(BASE_ID + statementLeftId))
              graph.node(BASE_ID + statementIdI).addEdge("ARGUMENT", graph.node(BASE_ID + statementRightId))
              graph.node(BASE_ID + statementIdI).addEdge("AST", graph.node(BASE_ID + statementLeftId)) // This edge seems to be added somewhere else. But idk where, so I'm adding it another time.
              graph.node(BASE_ID + statementIdI).addEdge("AST", graph.node(BASE_ID + statementRightId))
            } else if(statementLeftKind.equals("IndexAccess")) {
              val statementLeftId_ = registerStatement(graph, statementLeft, 1, BASE_ID, placeholderReplacement, placeholderArguments)(0)
              require(statementLeftId_ == statementLeftId)

              val codeLeft = graph.node(BASE_ID + statementLeftId).property("CODE")
              val codeRight = graph.node(BASE_ID + statementRightId).property("CODE")
              val code = codeLeft + " = " + codeRight

              graph.addNode(BASE_ID + statementIdI, "CALL")
              graph.node(BASE_ID + statementIdI).setProperty("ORDER", order)
              graph.node(BASE_ID + statementIdI).setProperty("ARGUMENT_INDEX", order)
              graph.node(BASE_ID + statementIdI).setProperty("CODE", code)
              graph.node(BASE_ID + statementIdI).setProperty("COLUMN_NUMBER", 0)
              graph.node(BASE_ID + statementIdI).setProperty("METHOD_FULL_NAME", operatorName)
              graph.node(BASE_ID + statementIdI).setProperty("TYPE_FULL_NAME", "ANY")
              graph.node(BASE_ID + statementIdI).setProperty("LINE_NUMBER", 0)
              graph.node(BASE_ID + statementIdI).setProperty("DISPATCH_TYPE", "STATIC_DISPATCH")
              graph.node(BASE_ID + statementIdI).setProperty("SIGNATURE", "TODO assignment signature")
              graph.node(BASE_ID + statementIdI).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
              graph.node(BASE_ID + statementIdI).setProperty("NAME", operatorName)
              order += 1

              graph.node(BASE_ID + statementIdI).addEdge("ARGUMENT", graph.node(BASE_ID + statementLeftId))
              graph.node(BASE_ID + statementIdI).addEdge("ARGUMENT", graph.node(BASE_ID + statementRightId))
              graph.node(BASE_ID + statementIdI).addEdge("AST", graph.node(BASE_ID + statementLeftId))
              graph.node(BASE_ID + statementIdI).addEdge("AST", graph.node(BASE_ID + statementRightId))
            } else {
              println("Invalid left kind!")
              println(statementLeftKind)
              require(false)
            }
          }

          return List.concat(localVariablesIds, statementIds).toArray
        }
      }
    }

    Array(statementId)
  }

  // TODO: optimize away using even more recursion
  def assignmentHelper(graph: Graph, BASE_ID: Long, operationId: Long, order: Int, statementLeftId: Long, statementLeftVariableName: String, operatorName: String, statementLeftReferencedId: Long, statementRightId: Long): Unit = {
    graph.addNode(BASE_ID + operationId, "CALL")
    graph.node(BASE_ID + operationId).setProperty("ORDER", order)
    graph.node(BASE_ID + operationId).setProperty("ARGUMENT_INDEX", order)
    graph.node(BASE_ID + operationId).setProperty("CODE", statementLeftVariableName + " = (...)")
    graph.node(BASE_ID + operationId).setProperty("COLUMN_NUMBER", 0)
    graph.node(BASE_ID + operationId).setProperty("METHOD_FULL_NAME", operatorName)
    graph.node(BASE_ID + operationId).setProperty("TYPE_FULL_NAME", "ANY")
    graph.node(BASE_ID + operationId).setProperty("LINE_NUMBER", 0)
    graph.node(BASE_ID + operationId).setProperty("DISPATCH_TYPE", "STATIC_DISPATCH")
    graph.node(BASE_ID + operationId).setProperty("SIGNATURE", "TODO assignment signature")
    graph.node(BASE_ID + operationId).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
    graph.node(BASE_ID + operationId).setProperty("NAME", operatorName)

    val referencedVariableNode = graph.node(BASE_ID + statementLeftReferencedId)
    val referencedVariableDataType = if(referencedVariableNode == null) "ERROR" else referencedVariableNode.property("TYPE_FULL_NAME")

    graph.addNode(BASE_ID + statementLeftId, "IDENTIFIER")
    graph.node(BASE_ID + statementLeftId).setProperty("ORDER", 1)
    graph.node(BASE_ID + statementLeftId).setProperty("ARGUMENT_INDEX", 1)
    graph.node(BASE_ID + statementLeftId).setProperty("CODE", statementLeftVariableName)
    graph.node(BASE_ID + statementLeftId).setProperty("COLUMN_NUMBER", 0)
    graph.node(BASE_ID + statementLeftId).setProperty("TYPE_FULL_NAME", referencedVariableDataType)
    graph.node(BASE_ID + statementLeftId).setProperty("LINE_NUMBER", 0)
    graph.node(BASE_ID + statementLeftId).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
    graph.node(BASE_ID + statementLeftId).setProperty("NAME", statementLeftVariableName)

    graph.node(BASE_ID + operationId).addEdge("AST", graph.node(BASE_ID + statementLeftId))
    graph.node(BASE_ID + operationId).addEdge("ARGUMENT", graph.node(BASE_ID + statementLeftId))

    graph.node(BASE_ID + operationId).addEdge("AST", graph.node(BASE_ID + statementRightId))
    graph.node(BASE_ID + operationId).addEdge("ARGUMENT", graph.node(BASE_ID + statementRightId))

    if(referencedVariableNode != null)
      graph.node(BASE_ID + statementLeftId).addEdge("REF", referencedVariableNode)
  }

  def memberAccessHelper(graph: Graph, BASE_ID: Long, memberAccess: Map[String, Object], placeholderReplacement: String, placeholderArguments: List[Map[String, Object]]): Int = {
    val memberAccessAttributes = memberAccess("attributes").asInstanceOf[Map[String, Object]]
    val memberAccessId = memberAccess("id").toString.toInt
    val memberName = memberAccessAttributes("member_name").toString
    val struct = memberAccess("children").asInstanceOf[List[Map[String, Object]]](0)
    val structAttributes = struct("attributes").asInstanceOf[Map[String, Object]]

    val structId = registerStatement(graph, struct, 1, BASE_ID, placeholderReplacement, placeholderArguments)(0)
    val structName = graph.node(BASE_ID + structId).property("CODE")
    val completeAccessCode = structName + "." + memberName

    graph.addNode(BASE_ID + memberAccessId, "CALL")
    graph.node(BASE_ID + memberAccessId).setProperty("ORDER", 1)
    graph.node(BASE_ID + memberAccessId).setProperty("ARGUMENT_INDEX", 1)
    graph.node(BASE_ID + memberAccessId).setProperty("CODE", completeAccessCode)
    graph.node(BASE_ID + memberAccessId).setProperty("COLUMN_NUMBER", 0)
    graph.node(BASE_ID + memberAccessId).setProperty("METHOD_FULL_NAME", "<operator>.fieldAccess")
    graph.node(BASE_ID + memberAccessId).setProperty("TYPE_FULL_NAME", "ANY")
    graph.node(BASE_ID + memberAccessId).setProperty("LINE_NUMBER", 0)
    graph.node(BASE_ID + memberAccessId).setProperty("DISPATCH_TYPE", "STATIC_DISPATCH")
    graph.node(BASE_ID + memberAccessId).setProperty("SIGNATURE", "TODO assignment signature")
    graph.node(BASE_ID + memberAccessId).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
    graph.node(BASE_ID + memberAccessId).setProperty("NAME", "<operator>.fieldAccess")

    // TODO: could make use of structAttributes("referencedDeclaration").toString.toInt for a ref edge

    graph.addNode(2*BASE_ID + structId, "FIELD_IDENTIFIER")
    graph.node(2*BASE_ID + structId).setProperty("ORDER", 2)
    graph.node(2*BASE_ID + structId).setProperty("LINE_NUMBER", 0)
    graph.node(2*BASE_ID + structId).setProperty("ARGUMENT_INDEX", 2)
    graph.node(2*BASE_ID + structId).setProperty("CODE", memberName)
    graph.node(2*BASE_ID + structId).setProperty("COLUMN_NUMBER", 0)
    graph.node(2*BASE_ID + structId).setProperty("CANONICAL_NAME", memberName)

    graph.node(BASE_ID + memberAccessId).addEdge("ARGUMENT", graph.node(BASE_ID + structId))
    graph.node(BASE_ID + memberAccessId).addEdge("AST", graph.node(BASE_ID + structId))
    graph.node(BASE_ID + memberAccessId).addEdge("ARGUMENT", graph.node(2*BASE_ID + structId))
    graph.node(BASE_ID + memberAccessId).addEdge("AST", graph.node(2*BASE_ID + structId))

    memberAccessId
  }

  def registerVariable(graph: Graph, wrappedVariableDeclaration: JsonAST.JValue): Unit = {
    // The CPG AST does not seem to care about global variables.
    // I implemented them as local variables as a makeshift solution.
    // In the Solidity AST, local and global variables are different.
    // Local variables are denoted within VariableDeclarationStatements, whereas
    // global variables are not. Both of them use VariableDeclaration nodes. But
    // for local variables, if there is an assignment to the newly defined
    // variable, the thing that the variable is assigned is a sibling of the
    // VariableDeclaration node, whereas for global variables it is the child with
    // index 1 of the VariableDeclaration node. Tuple variable declarations and tuple
    // variable definitions cannot occur outside of a function.
    var order = -1
    val declarationOperationId = getFieldInt(wrappedVariableDeclaration, "id")
    val children = getFieldList(wrappedVariableDeclaration, "children")
    require(children.length == 1 || children.length == 2)
    val variableAttributes = getField(wrappedVariableDeclaration, "attributes").asInstanceOf[Map[String, Object]]
    val variableDataType = variableAttributes("type").toString
    val variableName = variableAttributes("name").toString

    val BASE_ID = REAL_BASE_ID

    graph.addNode(BASE_ID + declarationOperationId, "LOCAL")
    graph.node(BASE_ID + declarationOperationId).setProperty("TYPE_FULL_NAME", variableDataType)
    graph.node(BASE_ID + declarationOperationId).setProperty("ORDER", order)
    graph.node(BASE_ID + declarationOperationId).setProperty("CODE", variableName)
    graph.node(BASE_ID + declarationOperationId).setProperty("DYNAMIC_TYPE_HINT_FULL_NAME", List())
    graph.node(BASE_ID + declarationOperationId).setProperty("NAME", variableName)
    order += 1

    graph.node(1000101).addEdge("AST", graph.node(BASE_ID + declarationOperationId))

    if(children.length == 2) {
      val BASE_ID = REAL_BASE_ID
      val placeholderReplacement = ""
      val placeholderArguments = List()
      val statementRightId = registerStatement(graph, children(1), 2, BASE_ID, placeholderReplacement, placeholderArguments)(0)
      assignmentHelper(graph, BASE_ID, 4 * BASE_ID + statementRightId, order, declarationOperationId + 1 * BASE_ID, variableName, getAssignmentOperatorName("="), declarationOperationId, statementRightId)

      graph.node(1000101).addEdge("AST", graph.node(BASE_ID + 4 * BASE_ID + statementRightId))
    }
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


  def getAssignmentOperatorName(symbol: String): String = {
    symbol match {
      case "+=" => "<operator>.assignmentPlus"
      case "-=" => "<operator>.assignmentMinus"
      case "*=" => "<operator>.assignmentMultiplication"
      case "/=" => "<operator>.assignmentDivision"
      case "=" => "<operator>.assignment"
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

        val astJsonFilePath = sys.env("AST_JSON_FILE_PATH")
        println(astJsonFilePath)
        val fileContents = Source.fromFile(astJsonFilePath).getLines.mkString
        val originalAst = parse(fileContents)

        /*childrenOpt match {
        case Some(children) => println(children._2)
        case None => println("no children")
      }*/
        val topLevelElements = originalAst.findField((jfield) => {
          jfield._1.equals("children")
        }).get._2
        val contracts = topLevelElements.children.filter(thing => {
          thing.values.asInstanceOf[Map[String, Object]]("name").equals("ContractDefinition")
        })

      var modifierDefinitions = List[Map[String, Object]]()

      for(contract <- contracts) {
        val contractLevelElements = contract.findField((jfield) => {
          jfield._1.equals("children")
        }).get._2
          .children

        // We need to loop through twice because otherwise we wouldn't be able
        // to access function definitions in function bodies.
        contractLevelElements.foreach(wrappedContractLevelElement => {
          // This is equivalent to this JS code:
          // let name = wrappedContractLevelElement.name
          val name = wrappedContractLevelElement.findField(jfield => {
            jfield._1.equals("name")
          }).get._2.values.toString

          name match {
            case "VariableDeclaration" => registerVariable(graph, wrappedContractLevelElement)
            case "FunctionDefinition" => registerFunctionHeader(graph, wrappedContractLevelElement)
            case "StructDefinition" => registerStructOrEnum(graph, wrappedContractLevelElement)
            case "EnumDefinition" => registerStructOrEnum(graph, wrappedContractLevelElement)
            case _ => {}
          }
        })

        // Collect modifier definitions.
        contractLevelElements.foreach(wrappedContractLevelElement => {
          val name = wrappedContractLevelElement.findField(jfield => {
            jfield._1.equals("name")
          }).get._2.values.toString
          name match {
            case "ModifierDefinition" => {
              val modifierDefinition = wrappedContractLevelElement.values.asInstanceOf[Map[String, Object]]
              modifierDefinitions = modifierDefinitions.appended(modifierDefinition)
            }
            case _ => {}
          }
        })
      }

      for(contract <- contracts) {
        val contractLevelElements = contract.findField((jfield) => {
          jfield._1.equals("children")
        }).get._2
          .children

        contractLevelElements.foreach(wrappedContractLevelElement => {
          val name = wrappedContractLevelElement.findField(jfield => {
            jfield._1.equals("name")
          }).get._2.values.toString
          name match {
            case "FunctionDefinition" => registerFunctionBody(graph, modifierDefinitions, wrappedContractLevelElement)
            case _ => {}
          }
        })
        println("processing completed")
      }
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
            ex.printStackTrace()
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
