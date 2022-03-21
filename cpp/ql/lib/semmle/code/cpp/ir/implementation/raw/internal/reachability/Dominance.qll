private import DominanceInternal

predicate blockImmediatelyDominates(Graph::Block dominator, Graph::Block block) =
  idominance(Graph::isEntryBlock/1, Graph::blockSuccessor/2)(_, dominator, block)

predicate blockImmediatelyPostDominates(Graph::Block postDominator, Graph::Block block) =
  idominance(Graph::isExitBlock/1, Graph::blockPredecessor/2)(_, postDominator, block)

predicate blockStrictlyDominates(Graph::Block dominator, Graph::Block block) {
  blockImmediatelyDominates+(dominator, block)
}

predicate blockStrictlyPostDominates(Graph::Block postdominator, Graph::Block block) {
  blockImmediatelyPostDominates+(postdominator, block)
}

predicate blockDominates(Graph::Block dominator, Graph::Block block) {
  blockStrictlyDominates(dominator, block) or dominator = block
}

predicate blockPostDominates(Graph::Block postdominator, Graph::Block block) {
  blockStrictlyPostDominates(postdominator, block) or postdominator = block
}

Graph::Block getDominanceFrontier(Graph::Block dominator) {
  Graph::blockSuccessor(dominator, result) and
  not blockImmediatelyDominates(dominator, result)
  or
  exists(Graph::Block prev | result = getDominanceFrontier(prev) |
    blockImmediatelyDominates(dominator, prev) and
    not blockImmediatelyDominates(dominator, result)
  )
}

Graph::Block getPostDominanceFrontier(Graph::Block postdominator) {
  Graph::blockPredecessor(postdominator, result) and
  not blockImmediatelyPostDominates(postdominator, result)
  or
  exists(Graph::Block prev | result = getPostDominanceFrontier(prev) |
    blockImmediatelyPostDominates(postdominator, prev) and
    not blockImmediatelyPostDominates(postdominator, result)
  )
}
