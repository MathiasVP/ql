using System.IO;

namespace Semmle.Extraction.CSharp.Entities
{
    class TypeParameterConstraints : FreshEntity
    {
        public TypeParameterConstraints(Context cx)
            : base(cx) { }

        public override TrapStackBehaviour TrapStackBehaviour => TrapStackBehaviour.NoLabel;

        protected override void Populate(TextWriter trapFile)
        {
        }
    }
}
