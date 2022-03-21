private import semmle.code.cpp.ir.implementation.aliased_ssa.internal.SSAConstructionInternal
private import semmle.code.cpp.ir.implementation.aliased_ssa.internal.SSAConstruction

predicate blockImmediatelyDominates(NewIR::IRBlock dominator, NewIR::IRBlock block) {
  Dominance::blockImmediatelyDominates(getOldBlock(dominator), getOldBlock(block))
}

predicate blockStrictlyDominates(NewIR::IRBlock dominator, NewIR::IRBlock block) {
  Dominance::blockStrictlyDominates(getOldBlock(dominator), getOldBlock(block))
}

predicate blockDominates(NewIR::IRBlock dominator, NewIR::IRBlock block) {
  Dominance::blockDominates(getOldBlock(dominator), getOldBlock(block))
}

NewIR::IRBlock getDominanceFrontier(NewIR::IRBlock dominator) {
  getOldBlock(result) = Dominance::getDominanceFrontier(getOldBlock(dominator))
}

predicate blockImmediatelyPostDominates(NewIR::IRBlock postdominator, NewIR::IRBlock block) {
  Dominance::blockImmediatelyPostDominates(getOldBlock(postdominator), getOldBlock(block))
}

predicate blockStrictlyPostDominates(NewIR::IRBlock postdominator, NewIR::IRBlock block) {
  Dominance::blockStrictlyPostDominates(getOldBlock(postdominator), getOldBlock(block))
}

NewIR::IRBlock getPostDominanceFrontier(NewIR::IRBlock postdominator) {
  getOldBlock(result) = Dominance::getPostDominanceFrontier(getOldBlock(postdominator))
}
