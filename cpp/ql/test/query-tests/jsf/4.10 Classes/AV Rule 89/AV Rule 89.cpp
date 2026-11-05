struct Base {};
typedef Base BaseAlias;

struct VirtualBase : virtual BaseAlias {};
struct NonVirtualBase : Base {};

struct Inconsistent : VirtualBase, NonVirtualBase {}; // $ Alert
struct IndirectInconsistent : Inconsistent {}; // $ Alert

struct OtherVirtualBase : virtual Base {};
struct AllVirtual : VirtualBase, OtherVirtualBase {};

struct OtherNonVirtualBase : Base {};
struct AllNonVirtual : NonVirtualBase, OtherNonVirtualBase {};

template<class T>
struct VirtualTemplate : virtual T {};

template<class T>
struct NonVirtualTemplate : T {};

struct TemplateInconsistent : VirtualTemplate<Base>, NonVirtualTemplate<Base> {}; // $ Alert

struct Unrelated {};
struct Disjoint : VirtualBase, Unrelated {};
