private import semmle.code.cpp.ir.implementation.unaliased_ssa.IR as Unaliased
private import AliasAnalysis as Alias
private import AliasConfiguration as Conf
private import semmle.code.cpp.models.interfaces.SideEffect as SideEffect

/** Holds if `f` calls (transitively) itself. */
private predicate loop(Unaliased::IRFunction f) { calls0+(f, f) }

/** Holds `f1` calls `f2`. */
private predicate calls0(Unaliased::IRFunction f1, Unaliased::IRFunction f2) {
  // Don't include calls we already model
  not NoTransitiveSideEffectWrite0::noTransitiveSideEffectWrite(f1) and
  not NoTransitiveSideEffectWrite0::noTransitiveSideEffectWrite(f2) and
  exists(Unaliased::CallInstruction call |
    call.getEnclosingIRFunction() = f1 and
    getStaticCallTarget(call) = f2
  )
}

private Unaliased::IRFunction getStaticCallTarget(Unaliased::CallInstruction call) {
  result.getFunction() = call.getStaticCallTarget()
}

/** Holds if `f1` is part of a cycle and `f1` calls `f2`. */
private predicate calls(Unaliased::IRFunction f1, Unaliased::IRFunction f2) {
  loop(f1) and
  calls0(f1, f2)
}

/**
 * A module for identifying functions that belong to the same "cycle" (i.e.,
 * where every function can end up calling another function).
 *
 * We group such functions into equivalence classes so that we can reason about their
 * side-effects as a group. For example, consider the following
 * ```cpp
 * void f1() { f2(); }
 *
 * void f2() { f3(); }
 *
 * void f3() { f1(); }
 * ```
 * Neither `f1`, `f2`, nor `f3` write to global memory, but naively checking
 * that the `f1` only writes to write to local memory by checking that all the
 * enclosing calls target functions that only write to local memory won't work
 * since `f1` ends up calling itself.
 */
private module Equiv = QlBuiltins::EquivalenceRelation<Unaliased::IRFunction, calls/2>;

/** Holds if `allocation` does not escape. */
private predicate allocationIsLocalOnly(Conf::Allocation allocation) {
  allocation.(Conf::VariableAllocation).isAlwaysAllocatedOnStack()
  or
  allocation.isUnaliased()
}

/** Holds if all allocations written to (and read from) in `func` are local allocations. */
private predicate noLocalSideEffectWrite(Unaliased::IRFunction func) {
  forall(Unaliased::AddressOperand addr | addr.getUse().getEnclosingIRFunction() = func |
    exists(Conf::Allocation allocation | allocation = Alias::getAddressOperandAllocation(addr) |
      allocationIsLocalOnly(allocation)
    )
  )
}

private signature module NoTransitiveSideEffectWriteSig {
  /**
   * Holds if the equivalence class `ec` contains a cycle of functions that
   * does not perform any writes to non-local memory.
   */
  predicate noTransitiveSideEffectWriteEquivClass(Equiv::EquivalenceClass ec);

  /**
   * Holds if `func` does not perform any writes to non-local memory.
   */
  predicate noTransitiveSideEffectWrite(Unaliased::IRFunction func);
}

private module NoTransitiveSideEffectWrite0 implements NoTransitiveSideEffectWriteSig {
  predicate noTransitiveSideEffectWriteEquivClass(Equiv::EquivalenceClass ec) { none() }

  predicate noTransitiveSideEffectWrite(Unaliased::IRFunction func) {
    func.getFunction().(SideEffect::SideEffectFunction).hasOnlySpecificWriteSideEffects()
  }
}

private predicate noLocalSideEffectsAndOnlyStaticCalls(Unaliased::IRFunction func) {
  noLocalSideEffectWrite(func) and
  forall(Unaliased::CallInstruction call | call.getEnclosingIRFunction() = func |
    exists(Unaliased::IRFunction callee | callee = getStaticCallTarget(call))
  )
}

private module NoTransitiveSideEffectWrite<NoTransitiveSideEffectWriteSig Prev> implements
  NoTransitiveSideEffectWriteSig
{
  predicate noTransitiveSideEffectWriteEquivClass(Equiv::EquivalenceClass ec) {
    // Either the cycle was resolved previously
    Prev::noTransitiveSideEffectWriteEquivClass(ec)
    or
    // Or we need to resolve the entire group now
    forex(Unaliased::IRFunction func | ec = Equiv::getEquivalenceClass(func) |
      // Only local side effects and static call targets
      noLocalSideEffectsAndOnlyStaticCalls(func) and
      forall(Unaliased::CallInstruction call, Unaliased::IRFunction callee |
        getStaticCallTarget(call) = callee and
        call.getEnclosingIRFunction() = func and
        // All calls going out of the group should be resolved
        ec != Equiv::getEquivalenceClass(callee)
      |
        Prev::noTransitiveSideEffectWrite(callee)
      )
    )
  }

  private predicate noTransitiveSideEffectWriteImpl(Unaliased::IRFunction func) {
    Prev::noTransitiveSideEffectWrite(func)
    or
    noLocalSideEffectsAndOnlyStaticCalls(func) and
    forall(Unaliased::CallInstruction call, Unaliased::IRFunction callee |
      getStaticCallTarget(call) = callee and
      call.getEnclosingIRFunction() = func
    |
      Prev::noTransitiveSideEffectWrite(callee)
    )
  }

  predicate noTransitiveSideEffectWrite(Unaliased::IRFunction func) {
    // Part of a cycle. Analyze every function in the cycle together
    exists(Equiv::EquivalenceClass ec |
      ec = Equiv::getEquivalenceClass(func) and
      noTransitiveSideEffectWriteEquivClass(ec)
    )
    or
    // Not part of a cycle: Do to normal thing
    not exists(Equiv::getEquivalenceClass(func)) and
    noTransitiveSideEffectWriteImpl(func)
  }
}

private module NoTransitiveSideEffectWrite1 =
  NoTransitiveSideEffectWrite<NoTransitiveSideEffectWrite0>;

private module NoTransitiveSideEffectWrite2 =
  NoTransitiveSideEffectWrite<NoTransitiveSideEffectWrite1>;

private module NoTransitiveSideEffectWrite3 =
  NoTransitiveSideEffectWrite<NoTransitiveSideEffectWrite2>;

private module NoTransitiveSideEffectWrite4 =
  NoTransitiveSideEffectWrite<NoTransitiveSideEffectWrite3>;

private module NoTransitiveSideEffectWrite5 =
  NoTransitiveSideEffectWrite<NoTransitiveSideEffectWrite4>;

private module NoTransitiveSideEffectWrite6 =
  NoTransitiveSideEffectWrite<NoTransitiveSideEffectWrite5>;

private module NoTransitiveSideEffectWrite7 =
  NoTransitiveSideEffectWrite<NoTransitiveSideEffectWrite6>;

private module NoTransitiveSideEffectWrite8 =
  NoTransitiveSideEffectWrite<NoTransitiveSideEffectWrite7>;

private module NoTransitiveSideEffectWrite9 =
  NoTransitiveSideEffectWrite<NoTransitiveSideEffectWrite8>;

private module NoTransitiveSideEffectWrite10 =
  NoTransitiveSideEffectWrite<NoTransitiveSideEffectWrite9>;

private module NoTransitiveSideEffectWrite11 =
  NoTransitiveSideEffectWrite<NoTransitiveSideEffectWrite10>;

module NoTransitiveSideEffectWrite12 = NoTransitiveSideEffectWrite<NoTransitiveSideEffectWrite11>;

private predicate noTransitiveSideEffectWrite =
  NoTransitiveSideEffectWrite11::noTransitiveSideEffectWrite/1;

/**
 * Holds if `instr` can be removed because it represents a side effect
 * instruction of a call for which we can prove does not write to non-local
 * memory.
 */
predicate removeableSideEffect(Unaliased::SideEffectInstruction instr) {
  (
    instr instanceof Unaliased::CallSideEffectInstruction or
    instr instanceof Unaliased::CallReadSideEffectInstruction
  ) and
  noTransitiveSideEffectWrite(getStaticCallTarget(instr.getPrimaryInstruction()))
}
