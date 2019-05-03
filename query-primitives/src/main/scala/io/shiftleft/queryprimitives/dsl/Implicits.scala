package io.shiftleft.queryprimitives.dsl

import io.shiftleft.codepropertygraph.generated.nodes
import io.shiftleft.queryprimitives.dsl.RealPipe.RealPipe
import io.shiftleft.queryprimitives.dsl.ShallowPipe.ShallowPipe
import io.shiftleft.queryprimitives.dsl.pipeops.{RealPipeOperations, ShallowPipeOperations}
import io.shiftleft.queryprimitives.steps.types.structure.MethodMethods

object Implicits extends PipeOperationImplicits with LowPriorityImplicits {
  implicit def realPipeMethods[ElemType](pipe: RealPipe[ElemType]) = {
    new RealPipeMethods(pipe)
  }

  implicit def methodMethods(pipe: RealPipe[nodes.Method]) = {
    new MethodMethods(pipe)
  }

}

class PipeOperationImplicits {
  private val realPipeOps = new RealPipeOperations[Nothing]()
  private val shallowPipeOps = new ShallowPipeOperations[Nothing]()

  implicit def getRealPipeOps[ElemType]: RealPipeOperations[ElemType] = {
    realPipeOps.asInstanceOf[RealPipeOperations[ElemType]]
  }

  implicit def getShallowPipeOps[ElemType]: ShallowPipeOperations[ElemType] = {
    shallowPipeOps.asInstanceOf[ShallowPipeOperations[ElemType]]
  }
}

sealed trait LowPriorityImplicits {

  implicit def methodMethods(pipe: ShallowPipe[nodes.Method]) = {
    new MethodMethods(pipe)
  }

}


