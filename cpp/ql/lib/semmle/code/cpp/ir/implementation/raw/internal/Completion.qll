newtype TCompletion =
  TNormalCompletion() or
  TExceptionCompletion()

abstract class Completion extends TCompletion {
  abstract string toString();
}

class NormalCompletion extends Completion, TNormalCompletion {
  override string toString() { result = "normal" }
}

class ExceptionCompletion extends Completion, TExceptionCompletion {
  override string toString() { result = "exception" }
}

predicate isNormalCompletion(Completion c) { c instanceof NormalCompletion }

predicate isExceptionCompletion(Completion c) { c instanceof ExceptionCompletion }
