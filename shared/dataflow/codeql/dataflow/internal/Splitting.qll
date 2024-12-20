private import codeql.util.Location

signature class NodeSig {
  string toString();
}

signature class NodeRegionSig;

signature module SplittingSig<LocationSig Location> {
  class NodeRegion;

  class SplitKind {
    string toString();

    Location getLocation();

    predicate inScope(NodeRegion n);
  }

  class Split {
    string toString();

    Location getLocation();

    SplitKind getKind();

    predicate holds(NodeRegion n);
  }
}

signature module GraphSig<NodeRegionSig NodeRegion> {
  predicate entry(NodeRegion n);

  predicate exit(NodeRegion n);

  predicate step(NodeRegion n1, NodeRegion n2);
}

module Splitting<LocationSig Location, SplittingSig<Location> S, GraphSig<S::NodeRegion> G> {
  private import S
  private import G

  pragma[nomagic]
  private predicate splitHolds(Split s, SplitKind k, NodeRegion nr) {
    s.holds(nr) and
    s.getKind() = k
  }

  // k is in scope at n, but no specific Split holds at n
  private predicate noInfoNode(NodeRegion nr, SplitKind k) {
    k.inScope(nr) and
    not splitHolds(_, k, nr)
  }

  // k is in scope at n, and n is not dominated by a Split of kind k
  private predicate noSplitFwd(NodeRegion nr, SplitKind k) {
    noInfoNode(nr, k) and
    (
      entry(nr)
      or
      exists(NodeRegion pred |
        step(pred, nr) and
        not k.inScope(pred) and
        not splitHolds(_, k, pred)
      )
    )
    or
    exists(NodeRegion mid |
      step(mid, nr) and
      noInfoNode(nr, k) and
      noSplitFwd(mid, k)
    )
  }

  private predicate noSplitRev(NodeRegion nr, SplitKind k) {
    noInfoNode(nr, k) and
    (
      exit(nr)
      or
      exists(NodeRegion succ |
        step(nr, succ) and
        not k.inScope(succ) and
        not splitHolds(_, k, succ)
      )
    )
    or
    exists(NodeRegion mid |
      step(nr, mid) and
      noInfoNode(nr, k) and
      noSplitRev(mid, k)
    )
  }

  // predicate revReach(Node n, string ent) {
  //   exists(Node ex |
  //     splitExit(_, ex, _, _) and
  //     step*(n, ex) and
  //     ex.toString() = "conf" and
  //     if entry(n) then ent = "entry" else ent = ""
  //   )
  // }
  // n is dominated by one or more Splits of kind k, but no specific Split of kind k holds at n
  private predicate canHaveSplitFwd(NodeRegion n, SplitKind k) {
    noInfoNode(n, k) and
    not noSplitFwd(n, k)
  }

  private predicate canHaveSplitRev(NodeRegion n, SplitKind k) {
    noInfoNode(n, k) and
    not noSplitRev(n, k)
  }

  private predicate splitEntryStep(NodeRegion n1, NodeRegion n2, Split s, SplitKind k) {
    step(n1, n2) and
    splitHolds(s, k, n1) and
    noInfoNode(n2, k)
  }

  private predicate splitExitStep(NodeRegion n1, NodeRegion n2, Split s, SplitKind k) {
    step(n1, n2) and
    splitHolds(s, k, n2) and
    noInfoNode(n1, k)
  }

  private predicate hasSplitFwd(NodeRegion n, Split s, SplitKind k) {
    splitEntryStep(_, n, s, k) and
    canHaveSplitFwd(n, k)
    or
    exists(NodeRegion mid |
      hasSplitFwd(mid, s, k) and
      step(mid, n) and
      canHaveSplitFwd(n, k)
    )
  }

  private predicate hasSplitRev(NodeRegion n, Split s, SplitKind k) {
    splitExitStep(n, _, s, k) and
    canHaveSplitRev(n, k) and
    s.getKind() = k
    or
    exists(NodeRegion mid |
      hasSplitRev(mid, s, k) and
      step(n, mid) and
      canHaveSplitRev(n, k)
    )
  }

  predicate barrier1(NodeRegion n1, NodeRegion n2) {
    exists(Split s1, Split s2, SplitKind k |
      step(n1, n2) and
      splitHolds(s1, pragma[only_bind_into](k), n1) and
      splitHolds(s2, pragma[only_bind_into](k), n2) and
      s1 != s2
    )
  }

  predicate barrier2(NodeRegion n1, NodeRegion n2) {
    exists(Split s1, Split s2, SplitKind k |
      splitExitStep(n1, n2, s1, k) and
      hasSplitFwd(n1, s2, k) and
      s1 != s2 and
      not hasSplitFwd(n1, s1, k)
    )
  }

  predicate barrier3(NodeRegion n1, NodeRegion n2) {
    exists(Split s1, Split s2, SplitKind k |
      splitEntryStep(n1, n2, s1, k) and
      hasSplitRev(n2, s2, k) and
      s1 != s2 and
      not hasSplitRev(n2, s1, k)
    )
  }
}
