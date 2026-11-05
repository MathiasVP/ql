---
category: fix
---
* Reduced redundant computation and intermediate relation sizes in `cpp/bad-strncpy-size`, `cpp/complex-condition`, `cpp/duplicate-include-guard`, `cpp/inconsistent-virtual-inheritance`, `cpp/resource-not-released-in-destructor`, `cpp/toctou-race-condition`, `cpp/use-in-own-initializer`, and `cpp/useless-expression`, without changing the reported results.
* Further reduced intermediate relation sizes in `cpp/lossy-function-result-cast`, `cpp/resource-not-released-in-destructor`, `cpp/tainted-permissions-check`, and `cpp/weak-cryptographic-algorithm` by sharing reachability computations and simplifying aggregation, without changing the reported results.
* Reduced intermediate computation in `cpp/complex-block`, `cpp/rethrow-no-exception`, `cpp/comma-before-misleading-indentation`, `cpp/wrong-type-format-argument`, `cpp/string-copy-return-value-as-boolean`, `cpp/non-https-url`, and `cpp/incorrect-string-type-conversion`, without changing the reported results.
