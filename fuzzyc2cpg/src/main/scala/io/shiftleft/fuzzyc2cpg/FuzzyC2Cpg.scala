package io.shiftleft.fuzzyc2cpg

import java.io.FileInputStream

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
/*
import com.fasterxml.jackson.databind.ObjectMapper
import com.fasterxml.jackson.databind.json.JsonMapper
import com.fasterxml.jackson.module.scala.DefaultScalaModule
import com.fasterxml.jackson.module.scala.experimental.ScalaObjectMapper
*/
/*
import scala.util.parsing.json._
*/
/*
import org.json.JSONArray
import org.json.JSONObject
*/
import org.json4s._
import org.json4s.native.JsonMethods._


/*
import scala.tools.nsc.doc.html.page.JSONArray
import scala.tools.nsc.doc.html.page.JSONObject
*/
import scala.collection.mutable.ListBuffer
import scala.util.control.NonFatal
import scala.jdk.CollectionConverters._

case class Global(usedTypes: ConcurrentHashMap[String, Boolean] = new ConcurrentHashMap[String, Boolean]())

class FuzzyC2Cpg() {
  import FuzzyC2Cpg.logger

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
    println("Nodes:")
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
    println("Edges:")
    var itrEdges = graph.edges()
    while(itrEdges.hasNext) {
      var edge = itrEdges.next()
      println(edge)

      var innerItr = edge.bothNodes()
      while(innerItr.hasNext)
        println(innerItr.next())

      println("")
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

    /*
    val astCreator = new AstCreationPass(sourceFileNames, cpg, functionKeyPools.head)
    astCreator.createAndApply() // MARK

    //printNodes(graph)
    //printEdges(graph)

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

    /*
    println("parsing json")
    val mapper = JsonMapper.builder()
      .addModule(DefaultScalaModule)
      .build()
    println("parsing json")
    mapper.registerModule(DefaultScalaModule)
    println("parsing json")
    val obj = mapper.readValue[Object]("{ a: 'bc', b: 'qre' }")
    println("parsed json")
    println(obj)
    println("parsed json")
*/
    /*
    println("parsing json")
    val result = JSON.parseFull("{ a: 'bc', b: 'qre' }")
    println("parsed json")
    println(result)
    println("parsed json")
*/

/*
    val json = "{ a: 'bc', b: 'qre' }"
    val obj = new JSONObject(json)
    val pageName = obj.getJSONObject("pageInfo").getString("pageName")
    println(pageName)
    val arr = obj.getJSONArray("posts")
    var i = 0
    while (i < arr.length) {
      val post_id = arr.getJSONObject(i).getString("post_id")
      println(post_id)

      i += 1
    }
 */

    println("parsing json")
    val obj = parse(""" { "numbers" : [1, 2, 3, 4] } """)
    println("parsed json")
    println(obj)
    println("parsed json")

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
