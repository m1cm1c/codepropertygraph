package io.shiftleft.console

import better.files.Dsl._
import better.files._
import io.shiftleft.codepropertygraph.generated.Languages
import io.shiftleft.console.LanguageHelper._
import io.shiftleft.console.cpgcreation.LanguageGuesser._
import io.shiftleft.console.cpgcreation.LlvmLanguageFrontend
import org.scalatest.{Matchers, WordSpec}

class LanguageHelperTests extends WordSpec with Matchers {

  "LanguageHelper.guessLanguage" should {

    "guess `Java` for .jars/wars/ears" in {
      guessLanguage("foo.jar") shouldBe Some(Languages.JAVA)
      guessLanguage("foo.war") shouldBe Some(Languages.JAVA)
      guessLanguage("foo.ear") shouldBe Some(Languages.JAVA)
    }

    "guess `C#` for .csproj" in {
      guessLanguage("foo.csproj") shouldBe Some(Languages.CSHARP)
    }

    "guess `Go` for a .go file" in {
      guessLanguage("foo.go") shouldBe Some(Languages.GOLANG)
    }

    "guess `Go` for a directory containing `Gopkg.lock`" in {
      File.usingTemporaryDirectory("oculartests") { tmpDir =>
        touch(tmpDir / "Gopkg.lock")
        guessLanguage(tmpDir.toString) shouldBe Some(Languages.GOLANG)
      }
    }

    "guess `Go` for a directory containing `Gopkg.toml` its root" in {
      File.usingTemporaryDirectory("oculartests") { tmpDir =>
        touch(tmpDir / "Gopkg.toml")
        guessLanguage(tmpDir.toString) shouldBe Some(Languages.GOLANG)
      }
    }

    "guess `Javascript` for a directory containing `package.json` in its root" in {
      File.usingTemporaryDirectory("oculartests") { tmpDir =>
        touch(tmpDir / "package.json")
        guessLanguage(tmpDir.toString) shouldBe Some(Languages.JAVASCRIPT)
      }
    }

    "guess `C` for a directory containing .ll (LLVM) file in its root" in {
      File.usingTemporaryDirectory("oculartests") { tmpDir =>
        touch(tmpDir / "foobar.ll")
        guessLanguage(tmpDir.toString) shouldBe Some(Languages.LLVM)
      }
    }

    "guess `C` for a directory that does not contain any special file" in {
      File.usingTemporaryDirectory("oculartests") { tmpDir =>
        guessLanguage(tmpDir.toString) shouldBe Some(Languages.C)
      }
    }

  }

  "LanguageHelper.cpgGeneratorForLanguage" should {

    "select LLVM frontend for directories containing ll files" in {
      val frontend = cpgGeneratorForLanguage(
        Languages.LLVM,
        new LanguageFrontendConfig(),
        File(".").path
      )
      frontend.get.isInstanceOf[LlvmLanguageFrontend] shouldBe true
    }
  }

}
