newtype TCompletion =
  TNormalCompletion() or
  TExceptionCompletion() or
  TConditionCompletion(boolean b) { b = true or b = false }

abstract class Completion extends TCompletion {
  abstract string toString();
}

class NormalCompletion extends Completion, TNormalCompletion {
  override string toString() { result = "normal" }
}

class ExceptionCompletion extends Completion, TExceptionCompletion {
  override string toString() { result = "exception" }
}

class ConditionCompletion extends Completion, TConditionCompletion {
  override string toString() { result = this.getBranch().toString() }

  boolean getBranch() { this = TConditionCompletion(result) }

  ConditionCompletion booleanNot() { result.getBranch() = this.getBranch().booleanNot() }
}

predicate isNormalCompletion(Completion c) { c instanceof NormalCompletion }

predicate isExceptionCompletion(Completion c) { c instanceof ExceptionCompletion }

predicate isConditionCompletion(Completion c, boolean branch) {
  c.(ConditionCompletion).getBranch() = branch
}
