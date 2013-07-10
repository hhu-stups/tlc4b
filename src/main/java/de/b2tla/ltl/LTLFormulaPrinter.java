package de.b2tla.ltl;

import de.b2tla.prettyprint.TLAPrinter;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.ltl.core.parser.analysis.DepthFirstAdapter;
import de.be4.ltl.core.parser.node.AAndLtl;
import de.be4.ltl.core.parser.node.AEnabledLtl;
import de.be4.ltl.core.parser.node.AExistsLtl;
import de.be4.ltl.core.parser.node.AFalseLtl;
import de.be4.ltl.core.parser.node.AFinallyLtl;
import de.be4.ltl.core.parser.node.AForallLtl;
import de.be4.ltl.core.parser.node.AGloballyLtl;
import de.be4.ltl.core.parser.node.AImpliesLtl;
import de.be4.ltl.core.parser.node.ANotLtl;
import de.be4.ltl.core.parser.node.AOrLtl;
import de.be4.ltl.core.parser.node.AStrongFairLtl;
import de.be4.ltl.core.parser.node.ATrueLtl;
import de.be4.ltl.core.parser.node.AUnparsedLtl;
import de.be4.ltl.core.parser.node.AWeakFairLtl;

public class LTLFormulaPrinter extends DepthFirstAdapter {

	private final LTLFormulaVisitor ltlFormulaVisitor;
	private final TLAPrinter tlaPrinter;

	public LTLFormulaPrinter(TLAPrinter tlaPrinter,
			LTLFormulaVisitor ltlFormulaVisitor) {
		this.ltlFormulaVisitor = ltlFormulaVisitor;
		this.tlaPrinter = tlaPrinter;

		ltlFormulaVisitor.getLTLFormulaStart().apply(this);
	}

	@Override
	public void caseAGloballyLtl(AGloballyLtl node) {
		tlaPrinter.moduleStringAppend("[](");
		node.getLtl().apply(this);
		tlaPrinter.moduleStringAppend(")");
	}

	@Override
	public void caseAFinallyLtl(AFinallyLtl node) {
		tlaPrinter.moduleStringAppend("<>(");
		node.getLtl().apply(this);
		tlaPrinter.moduleStringAppend(")");
	}

	@Override
	public void caseATrueLtl(ATrueLtl node) {
		tlaPrinter.moduleStringAppend("TRUE");
	}

	@Override
	public void caseAFalseLtl(AFalseLtl node) {
		tlaPrinter.moduleStringAppend("FALSE");
	}

	@Override
	public void caseAUnparsedLtl(AUnparsedLtl node) {
		ltlFormulaVisitor.getBAst(node).apply(tlaPrinter);
	}

	@Override
	public void caseAAndLtl(AAndLtl node) {
		node.getLeft().apply(this);
		tlaPrinter.moduleStringAppend(" /\\ ");
		node.getRight().apply(this);
	}

	@Override
	public void caseAOrLtl(AOrLtl node) {
		node.getLeft().apply(this);
		tlaPrinter.moduleStringAppend(" \\/ ");
		node.getRight().apply(this);
	}

	@Override
	public void caseANotLtl(ANotLtl node) {
		tlaPrinter.moduleStringAppend("\\neg(");
		node.getLtl().apply(this);
		tlaPrinter.moduleStringAppend(")");
	}

	@Override
	public void caseAImpliesLtl(AImpliesLtl node) {
		node.getLeft().apply(this);
		tlaPrinter.moduleStringAppend(" => ");
		node.getRight().apply(this);
	}

	@Override
	public void caseAEnabledLtl(AEnabledLtl node) {
		tlaPrinter.moduleStringAppend("ENABLED(");
		tlaPrinter.moduleStringAppend(node.getOperation().getText());
		tlaPrinter.moduleStringAppend(")");
	}

	@Override
	public void caseAWeakFairLtl(AWeakFairLtl node) {
		tlaPrinter.printWeakFairness(node.getOperation().getText());
	}

	@Override
	public void caseAStrongFairLtl(AStrongFairLtl node) {
		tlaPrinter.printStrongFairness(node.getOperation().getText());
	}

	@Override
	public void caseAExistsLtl(AExistsLtl node) {
		tlaPrinter.moduleStringAppend("\\E ");
		tlaPrinter.moduleStringAppend(node.getExistsIdentifier().getText());
		tlaPrinter.moduleStringAppend(" \\in ");
		Node id = this.ltlFormulaVisitor.getLTLIdentifier(node
				.getExistsIdentifier().getText());
		tlaPrinter.printTypeOfIdentifier((AIdentifierExpression) id);
		tlaPrinter.moduleStringAppend(": ");
		ltlFormulaVisitor.getBAst(node).apply(tlaPrinter);
		tlaPrinter.moduleStringAppend(" /\\ ");
		node.getLtl().apply(this);
	}

	@Override
	public void caseAForallLtl(AForallLtl node) {
		tlaPrinter.moduleStringAppend("\\A ");
		tlaPrinter.moduleStringAppend(node.getForallIdentifier().getText());
		tlaPrinter.moduleStringAppend(" \\in ");
		Node id = this.ltlFormulaVisitor.getLTLIdentifier(node
				.getForallIdentifier().getText());
		tlaPrinter.printTypeOfIdentifier((AIdentifierExpression) id);
		tlaPrinter.moduleStringAppend(": ");
		ltlFormulaVisitor.getBAst(node).apply(tlaPrinter);
		tlaPrinter.moduleStringAppend(" /\\ ");
		node.getLtl().apply(this);
	}

}
