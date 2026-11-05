struct Interface {
    virtual void operation() = 0;
};

struct OtherInterface {
    virtual void otherOperation() = 0;
};

struct Implementation {
    int data;
};

struct OtherImplementation {
    int otherData;
};

struct ThirdImplementation {
    int thirdData;
};

struct InterfacesOnly : Interface, OtherInterface {};
struct PrivateImplementation : Interface, private Implementation {};
struct OneProtectedImplementation : Interface, protected Implementation {};

struct PublicImplementation : Interface, public Implementation {}; // $ Alert[cpp/undisciplined-multiple-inheritance]

struct TwoProtectedImplementations : Interface, protected Implementation, protected OtherImplementation {}; // $ Alert[cpp/undisciplined-multiple-inheritance]

struct PublicAndTwoProtected : Interface, public Implementation, protected OtherImplementation, protected ThirdImplementation {}; // $ Alert[cpp/undisciplined-multiple-inheritance]

struct NoInterface : public Implementation, public OtherImplementation {};
