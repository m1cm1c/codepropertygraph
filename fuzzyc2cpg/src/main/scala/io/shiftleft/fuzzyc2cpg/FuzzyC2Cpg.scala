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
    println("CPG:")
    var itr = cpg.graph.nodes()
    while(itr.hasNext)
      println(itr.next())

    val astCreator = new AstCreationPass(sourceFileNames, cpg, functionKeyPools.head)
    astCreator.createAndApply() // MARK

    println("CPG:")
    itr = cpg.graph.nodes()
    while(itr.hasNext)
      println(itr.next())

    println("Edges:")
    var itrEdges = cpg.graph.edges()
    while(itrEdges.hasNext) {
      var edge = itrEdges.next()
      println(edge)

      var innerItr = edge.bothNodes()
      while(innerItr.hasNext)
        println(innerItr.next())

      println("")
    }
    // MARK: Einstiegspunkt
    // The first 4 nodes are: MetaData, NamespaceBlock, File, NamespaceBlock
    // All other nodes need to be deleted.
    itr = cpg.graph.nodes()
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

    println("CPG:")
    itr = cpg.graph.nodes()
    while(itr.hasNext)
      println(itr.next())

    println("Edges:")
    itrEdges = cpg.graph.edges()
    while(itrEdges.hasNext) {
      var edge = itrEdges.next()
      println(edge)

      var innerItr = edge.bothNodes()
      while(innerItr.hasNext)
        println(innerItr.next())

      println("")
    }
    // Recreating the initial CPG manually.
    val graph = cpg.graph
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


    println("CPG:")
    itr = cpg.graph.nodes()
    while(itr.hasNext)
      println(itr.next())

    println("Edges:")
    itrEdges = cpg.graph.edges()
    while(itrEdges.hasNext) {
      var edge = itrEdges.next()
      println(edge)

      var innerItr = edge.bothNodes()
      while(innerItr.hasNext)
        println(innerItr.next())

      println("")
    }

    new CfgCreationPass(cpg, functionKeyPools.last).createAndApply() // MARK
    new StubRemovalPass(cpg).createAndApply()
    new TypeNodePass(astCreator.global.usedTypes.keys().asScala.toList, cpg, Some(typesKeyPool)).createAndApply()
    cpg
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
