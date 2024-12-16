private import cpp
import Base
private import semmle.code.cpp.ir.IR

signature module StageSig {
  class Node {
    string toString();

    Instruction asInstruction();

    Operand asOperand();

    Declaration getEnclosingCallable();

    Declaration getFunction();

    DataFlowType getType();

    Location getLocation();

    predicate isGLValue();

    predicate hasIndexInBlock(IRBlock block, int i);

    string stars();
  }

  class OperandNode extends Node {
    Operand getOperand();
  }

  OperandNode operandNode(Operand operand);

  class InstructionNode extends Node {
    Instruction getInstruction();
  }

  InstructionNode instructionNode(Instruction instr);

  class IndirectOperandNode extends Node {
    predicate hasOperandAndIndirectionIndex(Operand operand, int indirectionIndex);
  }

  class IndirectInstructionNode extends Node {
    predicate hasInstructionAndIndirectionIndex(Instruction instr, int indirectionIndex);
  }

  class DataFlowCallable {
    Declaration getUnderlyingCallable();
  }

  DataFlowCallable nodeGetEnclosingCallable(Node n);

  class DataFlowCall;

  class Position;

  bindingset[s]
  Position decodePosition(string s);

  class ArgumentNode instanceof Node {
    predicate argumentOf(DataFlowCall call, Position pos);
  }

  class ReturnKind {
    /** Gets the indirection index of this return kind. */
    int getIndirectionIndex();

    /** Gets a textual representation of this return kind. */
    string toString();
  }

  class OutNode {
    /** Gets the underlying call. */
    DataFlowCall getCall();

    /** Gets the kind of this out node. */
    ReturnKind getReturnKind();
  }

  class ReturnNode {
    /** Gets the kind of this returned value. */
    ReturnKind getKind();
  }

  predicate hasOperandAndIndex(IndirectOperandNode n, Operand op, int indirectionIndex);

  predicate hasInstructionAndIndex(
    IndirectInstructionNode n, Instruction instr, int indirectionIndex
  );

  predicate nodeHasOperand(Node node, Operand operand, int indirectionIndex);

  predicate nodeHasInstruction(Node node, Instruction instr, int indirectionIndex);

  predicate localFlowStep(Node node1, Node node2);

  class PostUpdateNode extends Node {
    Node getPreUpdateNode();
  }
}
