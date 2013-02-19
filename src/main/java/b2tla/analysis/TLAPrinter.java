package b2tla.analysis;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;

import b2tla.analysis.nodes.EqualsNode;
import b2tla.analysis.nodes.NodeType;
import b2tla.btypes.BType;
import b2tla.btypes.FunctionType;
import b2tla.btypes.IntegerType;
import b2tla.btypes.SetType;
import b2tla.tla.TLADefinition;
import b2tla.tla.TLAModule;

import de.be4.classicalb.core.parser.Utils;
import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AAddExpression;
import de.be4.classicalb.core.parser.node.AAssignSubstitution;
import de.be4.classicalb.core.parser.node.ABooleanFalseExpression;
import de.be4.classicalb.core.parser.node.ABooleanTrueExpression;
import de.be4.classicalb.core.parser.node.ACardExpression;
import de.be4.classicalb.core.parser.node.AChoiceSubstitution;
import de.be4.classicalb.core.parser.node.AComprehensionSetExpression;
import de.be4.classicalb.core.parser.node.AConjunctPredicate;
import de.be4.classicalb.core.parser.node.ACoupleExpression;
import de.be4.classicalb.core.parser.node.ADisjunctPredicate;
import de.be4.classicalb.core.parser.node.ADivExpression;
import de.be4.classicalb.core.parser.node.ADomainExpression;
import de.be4.classicalb.core.parser.node.ADomainRestrictionExpression;
import de.be4.classicalb.core.parser.node.ADomainSubtractionExpression;
import de.be4.classicalb.core.parser.node.AEmptySetExpression;
import de.be4.classicalb.core.parser.node.AEnumeratedSetSet;
import de.be4.classicalb.core.parser.node.AEqualPredicate;
import de.be4.classicalb.core.parser.node.AExistsPredicate;
import de.be4.classicalb.core.parser.node.AExpressionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.AForallPredicate;
import de.be4.classicalb.core.parser.node.AFunctionExpression;
import de.be4.classicalb.core.parser.node.AGeneralIntersectionExpression;
import de.be4.classicalb.core.parser.node.AGeneralProductExpression;
import de.be4.classicalb.core.parser.node.AGeneralSumExpression;
import de.be4.classicalb.core.parser.node.AGeneralUnionExpression;
import de.be4.classicalb.core.parser.node.AGreaterEqualPredicate;
import de.be4.classicalb.core.parser.node.AGreaterPredicate;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.AIdentityExpression;
import de.be4.classicalb.core.parser.node.AIfSubstitution;
import de.be4.classicalb.core.parser.node.AImplicationPredicate;
import de.be4.classicalb.core.parser.node.AIntSetExpression;
import de.be4.classicalb.core.parser.node.AIntegerExpression;
import de.be4.classicalb.core.parser.node.AIntegerSetExpression;
import de.be4.classicalb.core.parser.node.AIntersectionExpression;
import de.be4.classicalb.core.parser.node.AIntervalExpression;
import de.be4.classicalb.core.parser.node.ALambdaExpression;
import de.be4.classicalb.core.parser.node.ALessEqualPredicate;
import de.be4.classicalb.core.parser.node.ALessPredicate;
import de.be4.classicalb.core.parser.node.AMachineHeader;
import de.be4.classicalb.core.parser.node.AMaxExpression;
import de.be4.classicalb.core.parser.node.AMemberPredicate;
import de.be4.classicalb.core.parser.node.AMinExpression;
import de.be4.classicalb.core.parser.node.AMinusOrSetSubtractExpression;
import de.be4.classicalb.core.parser.node.AModuloExpression;
import de.be4.classicalb.core.parser.node.AMultOrCartExpression;
import de.be4.classicalb.core.parser.node.ANat1SetExpression;
import de.be4.classicalb.core.parser.node.ANatSetExpression;
import de.be4.classicalb.core.parser.node.ANatural1SetExpression;
import de.be4.classicalb.core.parser.node.ANaturalSetExpression;
import de.be4.classicalb.core.parser.node.ANotMemberPredicate;
import de.be4.classicalb.core.parser.node.ANotSubsetPredicate;
import de.be4.classicalb.core.parser.node.ANotSubsetStrictPredicate;
import de.be4.classicalb.core.parser.node.AOperation;
import de.be4.classicalb.core.parser.node.AParallelSubstitution;
import de.be4.classicalb.core.parser.node.APartialFunctionExpression;
import de.be4.classicalb.core.parser.node.APow1SubsetExpression;
import de.be4.classicalb.core.parser.node.APowSubsetExpression;
import de.be4.classicalb.core.parser.node.APowerOfExpression;
import de.be4.classicalb.core.parser.node.APredecessorExpression;
import de.be4.classicalb.core.parser.node.APredicateDefinitionDefinition;
import de.be4.classicalb.core.parser.node.ARangeExpression;
import de.be4.classicalb.core.parser.node.ARelationsExpression;
import de.be4.classicalb.core.parser.node.ASequenceExtensionExpression;
import de.be4.classicalb.core.parser.node.ASetExtensionExpression;
import de.be4.classicalb.core.parser.node.ASubsetPredicate;
import de.be4.classicalb.core.parser.node.ASubsetStrictPredicate;
import de.be4.classicalb.core.parser.node.ASuccessorExpression;
import de.be4.classicalb.core.parser.node.AUnaryMinusExpression;
import de.be4.classicalb.core.parser.node.AUnionExpression;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PPredicate;
import de.be4.classicalb.core.parser.node.PSubstitution;
import de.be4.classicalb.core.parser.node.TIdentifierLiteral;

public class TLAPrinter extends DepthFirstAdapter {

	private HashSet<Node> initNodes;

	private StringBuilder tlaModuleString;
	private StringBuilder configFileString;

	public StringBuilder getConfigString() {
		return configFileString;
	}

	public StringBuilder getStringbuilder() {
		return tlaModuleString;
	}

	private MachineContext machineContext;
	private Typechecker typechecker;
	private UnchangedVariablesFinder unchangedVariablesFinder;
	private PrecedenceCollector precedenceCollector;
	private UsedStandardModules usedStandardModules;
	private TypeRestrictor typeRestrictor;
	private TLAModule tlaModule;


	public TLAPrinter(MachineContext machineContext, Typechecker typechecker,
			UnchangedVariablesFinder unchangedVariablesFinder,
			PrecedenceCollector precedenceCollector,
			UsedStandardModules usedStandardModules,
			TypeRestrictor typeRestrictor, TLAModule tlaModule) {
		this.initNodes = new HashSet<Node>();
		this.typechecker = typechecker;
		this.machineContext = machineContext;
		this.unchangedVariablesFinder = unchangedVariablesFinder;
		this.precedenceCollector = precedenceCollector;
		this.usedStandardModules = usedStandardModules;
		this.typeRestrictor = typeRestrictor;
		this.tlaModule = tlaModule;

		this.tlaModuleString = new StringBuilder();
		this.configFileString = new StringBuilder();

		//Start start = machineContext.getTree();
		// start.apply(this);
	}

	public void start() {
		printHeader();
		printExtendedModules();
		printConstants();
		printDefinitions();
		printAssume();
		printVariables();
		printInvariant();
		printInit();
		printOperations();

		printConstantValues();
		tlaModuleString.append("====");

		printConfig();
	}

	private void printConstantValues() {
		ArrayList<Node> list = this.tlaModule.getConstants();
		if (list.size() != 0) {
			Hashtable<Node, NodeType> table = this.typeRestrictor
					.getRestrictedTypes();

			for (int i = 0; i < list.size(); i++) {
				Node con = list.get(i);
				if (table.containsKey(con)) {
					con.apply(this);
					tlaModuleString.append("_def == ");
					EqualsNode e = (EqualsNode) table.get(con);
					e.getExpression().apply(this);
					tlaModuleString.append("\n");
				}
			}
		}

	}

	private void printConfig() {
		if (this.tlaModule.getInitPredicates().size() > 0) {
			this.configFileString.append("INIT Init\n");
		}
		if (this.tlaModule.getOperations().size() > 0) {
			this.configFileString.append("NEXT Next\n");
		}
		if (this.tlaModule.getVariables().size() > 0) {
			this.configFileString.append("INVARIANT Invariant");
		}

		// CONSTANTS
		ArrayList<Node> list = this.tlaModule.getConstants();
		if (list.size() != 0) {
			configFileString.append("CONSTANTS\n");

			for (int i = 0; i < list.size(); i++) {
				Node con = list.get(i);
				BType t = typechecker.getType(con);
				
				if(t instanceof SetType){
					//TODO Deffered set
					String conString = getIdentifier((AIdentifierExpression) con);
					configFileString.append(conString + " = " + conString
							+ " + more\n");
				}else{
					String conString = getIdentifier((AIdentifierExpression) con);
					configFileString.append(conString + " = " + conString
							+ "\n");
				}

			}
		}

	}

	private String getIdentifier(AIdentifierExpression node) {
		String res = "";
		List<TIdentifierLiteral> copy = new ArrayList<TIdentifierLiteral>(
				node.getIdentifier());
		for (TIdentifierLiteral e : copy) {
			res += e.getText();
		}
		return res;
	}

	private void printHeader() {
		tlaModuleString.append("---- MODULE ");
		tlaModuleString.append(this.tlaModule.getModuleName());
		tlaModuleString.append(" ----\n");
	}

	private void printExtendedModules() {
		if (usedStandardModules.getUsedModules().size() > 0) {
			tlaModuleString.append("EXTENDS ");
			for (int i = 0; i < usedStandardModules.getUsedModules().size(); i++) {
				if (i > 0) {
					tlaModuleString.append(", ");
				}
				tlaModuleString.append(usedStandardModules.getUsedModules()
						.get(i));
			}
			tlaModuleString.append("\n");
		}
	}

	private void printDefinitions() {
		ArrayList<TLADefinition> definitions = tlaModule.getDefinitions();
		for (int i = 0; i < definitions.size(); i++) {
			TLADefinition def = definitions.get(i);
			def.getDefName().apply(this);
			tlaModuleString.append(" == ");
			Node e = def.getDefinition();
			if (e == null) {
				tlaModuleString.append("{");
				def.getDefName().apply(this);
				tlaModuleString.append("_1, ");
				def.getDefName().apply(this);
				tlaModuleString.append("_2}");
			} else {
				e.apply(this);
			}
			tlaModuleString.append("\n");
		}
	}

	private void printConstants() {
		ArrayList<Node> list = this.tlaModule.getConstants();
		if (list.size() == 0)
			return;
		tlaModuleString.append("CONSTANTS ");
		for (int i = 0; i < list.size(); i++) {
			list.get(i).apply(this);
			if (i < list.size() - 1)
				tlaModuleString.append(", ");
		}
		tlaModuleString.append("\n");
	}

	private void printAssume() {
		ArrayList<Node> list = this.tlaModule.getAssume();
		if (list.size() == 0)
			return;

		for (int i = 0; i < list.size(); i++) {
			tlaModuleString.append("ASSUME ");
			list.get(i).apply(this);
			tlaModuleString.append("\n");
		}

	}

	private void printVariables() {
		ArrayList<Node> vars = this.tlaModule.getVariables();
		if (vars.size() == 0)
			return;
		tlaModuleString.append("VARIABLES ");
		for (int i = 0; i < vars.size(); i++) {
			vars.get(i).apply(this);
			if (i < vars.size() - 1)
				tlaModuleString.append(", ");
		}
		tlaModuleString.append("\n");
	}

	private void printInvariant() {
		PPredicate node = this.tlaModule.getInvariant();
		if (node == null)
			return;

		tlaModuleString.append("Invariant == ");
		node.apply(this);
		tlaModuleString.append("\n");
	}

	private void printInit() {
		ArrayList<Node> inits = this.tlaModule.getInitPredicates();
		if (inits.size() == 0)
			return;
		tlaModuleString.append("Init == ");
		for (int i = 0; i < inits.size(); i++) {
			initNodes.add(inits.get(i));
			inits.get(i).apply(this);

			if (i < inits.size() - 1)
				tlaModuleString.append(" /\\ ");
		}
		tlaModuleString.append("\n");
	}

	private void printOperations() {
		ArrayList<Node> ops = this.tlaModule.getOperations();
		if (ops.size() == 0)
			return;
		for (int i = 0; i < ops.size(); i++) {
			ops.get(i).apply(this);
		}
		tlaModuleString.append("Next == ");
		Iterator<String> itr = this.machineContext.getOperations().keySet()
				.iterator();
		while (itr.hasNext()) {
			String name = itr.next();
			tlaModuleString.append(name);
			if (itr.hasNext()) {
				tlaModuleString.append(" \\/ ");
			}
		}
		tlaModuleString.append("\n");
	}

	@Override
	public void defaultIn(final Node node) {
		if (precedenceCollector.getBrackets().contains(node)) {
			tlaModuleString.append("(");
		}
	}

	@Override
	public void defaultOut(final Node node) {
		if (precedenceCollector.getBrackets().contains(node)) {
			tlaModuleString.append(")");
		}
	}

	/*
	 * Treewalker
	 */

	@Override
	public void caseAMachineHeader(AMachineHeader node) {
		inAMachineHeader(node);
		tlaModuleString.append(node);
		{
			List<TIdentifierLiteral> copy = new ArrayList<TIdentifierLiteral>(
					node.getName());
			for (TIdentifierLiteral e : copy) {
				e.apply(this);
			}
		}
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getParameters());
			for (PExpression e : copy) {
				e.apply(this);
			}
		}
		outAMachineHeader(node);
	}

	@Override
	public void caseAEnumeratedSetSet(AEnumeratedSetSet node) {
		inAEnumeratedSetSet(node);
		{
			List<TIdentifierLiteral> copy = new ArrayList<TIdentifierLiteral>(
					node.getIdentifier());

			String setName = Utils.getIdentifierAsString(copy);
			tlaModuleString.append(setName + " == {");
		}
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getElements());
			for (int i = 0; i < copy.size(); i++) {
				copy.get(i).apply(this);
				if (i < copy.size() - 1) {
					tlaModuleString.append(", ");
				}
			}
		}
		tlaModuleString.append("}\n");
		outAEnumeratedSetSet(node);

	}

	/**
	 * Substitutions
	 * 
	 */

	@Override
	public void caseAAssignSubstitution(AAssignSubstitution node) {
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getLhsExpression());
		List<PExpression> copy2 = new ArrayList<PExpression>(
				node.getRhsExpressions());

		for (int i = 0; i < copy.size(); i++) {
			copy.get(i).apply(this);
			if (!initNodes.contains(node)) {
				tlaModuleString.append("'");
			}
			tlaModuleString.append(" = ");
			copy2.get(i).apply(this);

			if (i < copy.size() - 1) {
				tlaModuleString.append(" /\\ ");
			}
		}

		unchangedVariables(node);

	}

	public void unchangedVariables(Node node) {
		if (!initNodes.contains(node)) {
			ArrayList<Node> unchangedVariables = new ArrayList<Node>(
					unchangedVariablesFinder.getUnchangedVariablesTable().get(
							node));
			if (unchangedVariables.size() > 0) {
				tlaModuleString.append(" /\\ UNCHANGED <<");
				for (int i = 0; i < unchangedVariables.size(); i++) {
					unchangedVariables.get(i).apply(this);
					if (i < unchangedVariables.size() - 1) {
						tlaModuleString.append(", ");
					}
				}
				tlaModuleString.append(">>");
			}
		}
	}

	@Override
	public void caseAChoiceSubstitution(AChoiceSubstitution node) {
		List<PSubstitution> copy = new ArrayList<PSubstitution>(
				node.getSubstitutions());

		for (int i = 0; i < copy.size(); i++) {
			tlaModuleString.append("(");
			copy.get(i).apply(this);
			tlaModuleString.append(")");
			if (i < copy.size() - 1) {
				tlaModuleString.append(" \\/ ");
			}

		}

		unchangedVariables(node);
	}

	@Override
	public void caseAIfSubstitution(AIfSubstitution node) {
		tlaModuleString.append(" IF ");
		node.getCondition().apply(this);
		tlaModuleString.append(" THEN ");
		node.getThen().apply(this);
		List<PSubstitution> copy = new ArrayList<PSubstitution>(
				node.getElsifSubstitutions());
		for (PSubstitution e : copy) {
			e.apply(this);
		}
		tlaModuleString.append(" ELSE ");
		node.getElse().apply(this);

		unchangedVariables(node);
	}

	@Override
	public void caseAParallelSubstitution(AParallelSubstitution node) {
		for (Iterator<PSubstitution> itr = node.getSubstitutions().iterator(); itr
				.hasNext();) {
			PSubstitution e = itr.next();

			e.apply(this);

			if (itr.hasNext()) {
				tlaModuleString.append(" /\\ ");
			}
		}

		unchangedVariables(node);
	}

	@Override
	public void caseAOperation(AOperation node) {
		inAOperation(node);
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getReturnValues());
			for (PExpression e : copy) {
				e.apply(this);
			}
		}
		{
			List<TIdentifierLiteral> copy = new ArrayList<TIdentifierLiteral>(
					node.getOpName());
			for (TIdentifierLiteral e : copy) {
				tlaModuleString.append(e.getText());
				e.apply(this);
			}
		}
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getParameters());
			for (PExpression e : copy) {
				e.apply(this);
			}
		}
		tlaModuleString.append(" == ");
		if (node.getOperationBody() != null) {
			node.getOperationBody().apply(this);
		}

		tlaModuleString.append("\n");
		outAOperation(node);
	}

	/** Expression **/

	@Override
	public void caseAIdentifierExpression(AIdentifierExpression node) {
		inAIdentifierExpression(node);
		{
			List<TIdentifierLiteral> copy = new ArrayList<TIdentifierLiteral>(
					node.getIdentifier());
			for (TIdentifierLiteral e : copy) {

				tlaModuleString.append(e.getText());
				// e.apply(this);
			}
		}
		outAIdentifierExpression(node);
	}

	/**
	 * Logical Predicates
	 */

	@Override
	public void caseAEqualPredicate(AEqualPredicate node) {
		if (node.getLeft() != null) {
			node.getLeft().apply(this);
		}
		tlaModuleString.append(" = ");
		if (node.getRight() != null) {
			node.getRight().apply(this);
		}
	}

	@Override
	public void caseAConjunctPredicate(AConjunctPredicate node) {
		inAConjunctPredicate(node);
		node.getLeft().apply(this);
		tlaModuleString.append(" /\\ ");
		node.getRight().apply(this);
		outAConjunctPredicate(node);
	}

	@Override
	public void caseADisjunctPredicate(ADisjunctPredicate node) {
		inADisjunctPredicate(node);
		node.getLeft().apply(this);
		tlaModuleString.append(" \\/ ");
		node.getRight().apply(this);
		outADisjunctPredicate(node);
	}

	@Override
	public void caseAImplicationPredicate(AImplicationPredicate node) {
		inAImplicationPredicate(node);
		node.getLeft().apply(this);
		tlaModuleString.append(" => ");
		node.getRight().apply(this);
		outAImplicationPredicate(node);
	}
	
	
    @Override
    public void caseABooleanTrueExpression(ABooleanTrueExpression node)
    {
        inABooleanTrueExpression(node);
        tlaModuleString.append("TRUE");
        outABooleanTrueExpression(node);
    }
    
    @Override
    public void caseABooleanFalseExpression(ABooleanFalseExpression node)
    {
        inABooleanFalseExpression(node);
        tlaModuleString.append("FALSE");
        outABooleanFalseExpression(node);
    }


	@Override
	public void caseAForallPredicate(AForallPredicate node) {
		/*
		 * B: !x,y(T => P) TLA: \A x \in type(x), y \in type(y): T => P
		 */
		inAForallPredicate(node);
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());

		tlaModuleString.append("\\A ");
		for (int i = 0; i < copy.size(); i++) {
			PExpression e = copy.get(i);
			e.apply(this);
			tlaModuleString.append(" \\in ");
			printTypeOfIdentifier(e);
			if (i < copy.size() - 1) {
				tlaModuleString.append(", ");
			}
		}

		tlaModuleString.append(" : ");

		node.getImplication().apply(this);
		outAForallPredicate(node);
	}

	@Override
	public void caseAExistsPredicate(AExistsPredicate node) {
		/*
		 * B: #x,y(T => P) TLA: \E x \in type(x), y \in type(y): T => P
		 */
		inAExistsPredicate(node);
		tlaModuleString.append("\\E ");
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (int i = 0; i < copy.size(); i++) {
			PExpression e = copy.get(i);
			e.apply(this);
			tlaModuleString.append(" \\in ");
			printTypeOfIdentifier(e);
			if (i < copy.size() - 1) {
				tlaModuleString.append(", ");
			}
		}
		tlaModuleString.append(" : ");
		node.getPredicate().apply(this);
		outAExistsPredicate(node);
	}

	@Override
	public void caseAIntegerExpression(AIntegerExpression node) {
		inAIntegerExpression(node);
		if (node.getLiteral() != null) {
			tlaModuleString.append(node.getLiteral().getText());
			// node.getLiteral().apply(this);
		}
		outAIntegerExpression(node);
	}

	@Override
	public void caseAPredicateDefinitionDefinition(
			APredicateDefinitionDefinition node) {
		if (node.getName() != null) {
			tlaModuleString.append(node.getName().getText());
			node.getName().apply(this);
		}
		tlaModuleString.append(" == ");

		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getParameters());
			for (PExpression e : copy) {
				e.apply(this);
			}
		}
		if (node.getRhs() != null) {
			node.getRhs().apply(this);
		}
		tlaModuleString.append("\n");
	}

	@Override
	public void caseAExpressionDefinitionDefinition(
			AExpressionDefinitionDefinition node) {
		if (node.getName() != null) {
			tlaModuleString.append(node.getName().getText());
			node.getName().apply(this);
		}
		tlaModuleString.append(" == ");
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getParameters());
			for (PExpression e : copy) {
				e.apply(this);
			}
		}
		if (node.getRhs() != null) {
			node.getRhs().apply(this);
		}
		tlaModuleString.append("\n");
	}

	/**
	 * Numbers
	 */

	@Override
	public void caseAIntegerSetExpression(AIntegerSetExpression node) {
		inAIntegerSetExpression(node);
		tlaModuleString.append("Int");
		outAIntegerSetExpression(node);
	}

	@Override
	public void caseANaturalSetExpression(ANaturalSetExpression node) {
		inANaturalSetExpression(node);
		tlaModuleString.append("Nat");
		outANaturalSetExpression(node);
	}

	@Override
	public void caseANatural1SetExpression(ANatural1SetExpression node) {
		inANatural1SetExpression(node);
		tlaModuleString.append("Nat \\ {0}");
		outANatural1SetExpression(node);
	}

	@Override
	public void caseAIntSetExpression(AIntSetExpression node) {
		inAIntSetExpression(node);
		tlaModuleString.append("Int");
		outAIntSetExpression(node);
	}

	@Override
	public void caseANatSetExpression(ANatSetExpression node) {
		inANatSetExpression(node);
		tlaModuleString.append("Nat");
		outANatSetExpression(node);
	}

	@Override
	public void caseANat1SetExpression(ANat1SetExpression node) {
		inANat1SetExpression(node);
		tlaModuleString.append("Nat \\ {0}");
		outANat1SetExpression(node);
	}

	@Override
	public void caseAIntervalExpression(AIntervalExpression node) {
		inAIntervalExpression(node);
		node.getLeftBorder().apply(this);
		tlaModuleString.append(" .. ");
		node.getRightBorder().apply(this);
		outAIntervalExpression(node);
	}

	@Override
	public void caseAGreaterPredicate(AGreaterPredicate node) {
		inAGreaterPredicate(node);
		node.getLeft().apply(this);
		tlaModuleString.append(" > ");
		node.getRight().apply(this);
		outAGreaterPredicate(node);
	}

	@Override
	public void caseALessPredicate(ALessPredicate node) {
		inALessPredicate(node);
		node.getLeft().apply(this);
		tlaModuleString.append(" < ");
		node.getRight().apply(this);
		outALessPredicate(node);
	}

	@Override
	public void caseAGreaterEqualPredicate(AGreaterEqualPredicate node) {
		inAGreaterEqualPredicate(node);
		node.getLeft().apply(this);
		tlaModuleString.append(" >= ");
		node.getRight().apply(this);
		outAGreaterEqualPredicate(node);
	}

	@Override
	public void caseALessEqualPredicate(ALessEqualPredicate node) {
		inALessEqualPredicate(node);
		node.getLeft().apply(this);
		tlaModuleString.append(" =< ");
		node.getRight().apply(this);
		outALessEqualPredicate(node);
	}

	@Override
	public void caseAMinExpression(AMinExpression node) {
		inAMinExpression(node);
		tlaModuleString.append("CHOOSE min \\in ");
		node.getExpression().apply(this);
		tlaModuleString.append(" : \\A p \\in ");
		node.getExpression().apply(this);
		tlaModuleString.append(" : min =< p");
		outAMinExpression(node);
	}

	@Override
	public void caseAMaxExpression(AMaxExpression node) {
		inAMaxExpression(node);
		tlaModuleString.append("CHOOSE max \\in ");
		node.getExpression().apply(this);
		tlaModuleString.append(" : \\A p \\in ");
		node.getExpression().apply(this);
		tlaModuleString.append(" : max >= p");
		outAMaxExpression(node);
	}

	@Override
	public void caseAUnaryMinusExpression(AUnaryMinusExpression node) {
		inAUnaryMinusExpression(node);
		tlaModuleString.append("-");
		node.getExpression().apply(this);
		outAUnaryMinusExpression(node);
	}

	@Override
	public void caseAAddExpression(AAddExpression node) {
		node.getLeft().apply(this);
		tlaModuleString.append(" + ");
		node.getRight().apply(this);
	}

	@Override
	public void caseADivExpression(ADivExpression node) {
		inADivExpression(node);
		node.getLeft().apply(this);
		tlaModuleString.append(" \\div ");
		node.getRight().apply(this);
		outADivExpression(node);
	}

	@Override
	public void caseAPowerOfExpression(APowerOfExpression node) {
		inAPowerOfExpression(node);
		node.getLeft().apply(this);
		tlaModuleString.append(" ^ ");
		node.getRight().apply(this);
		outAPowerOfExpression(node);
	}

	@Override
	public void caseAModuloExpression(AModuloExpression node) {
		/**
		 * TODO a mod b: IF a < 0 THEN ERROR ELSE a % b
		 */
		inAModuloExpression(node);
		node.getLeft().apply(this);
		tlaModuleString.append(" % ");
		node.getRight().apply(this);
		outAModuloExpression(node);
	}

	@Override
	public void caseAGeneralProductExpression(AGeneralProductExpression node) {
		inAGeneralProductExpression(node);
		tlaModuleString.append("PI({");

		node.getExpression().apply(this);
		tlaModuleString.append(" : ");

		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		printIdentifierList(copy);

		tlaModuleString.append(" \\in { ");

		printIdentifierList(copy);

		tlaModuleString.append(" \\in ");
		printTypesOfIdentifierList(copy);
		tlaModuleString.append(" : ");
		node.getPredicates().apply(this);
		tlaModuleString.append("}");

		tlaModuleString.append("}");
		outAGeneralProductExpression(node);
	}

	@Override
	public void caseAGeneralSumExpression(AGeneralSumExpression node) {
		inAGeneralSumExpression(node);
		tlaModuleString.append("SIGMA({");

		node.getExpression().apply(this);
		tlaModuleString.append(" : ");

		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		printIdentifierList(copy);

		tlaModuleString.append(" \\in { ");

		printIdentifierList(copy);

		tlaModuleString.append(" \\in ");
		printTypesOfIdentifierList(copy);
		tlaModuleString.append(" : ");
		node.getPredicates().apply(this);
		tlaModuleString.append("}");

		tlaModuleString.append("}");

		outAGeneralSumExpression(node);
	}

	@Override
	public void caseASuccessorExpression(ASuccessorExpression node) {
		inASuccessorExpression(node);
		tlaModuleString.append("succ");
		outASuccessorExpression(node);
	}

	@Override
	public void caseAPredecessorExpression(APredecessorExpression node) {
		inAPredecessorExpression(node);
		tlaModuleString.append("pred");
		outAPredecessorExpression(node);
	}

	/**
	 * Function
	 */

	private void printIdentifierList(List<PExpression> copy) {
		if (copy.size() > 1) {
			tlaModuleString.append("<<");
		}
		for (int i = 0; i < copy.size(); i++) {
			copy.get(i).apply(this);
			if (i < copy.size() - 1)
				tlaModuleString.append(", ");
		}
		if (copy.size() > 1) {
			tlaModuleString.append(">>");
		}
	}

	private void printTypeOfIdentifier(PExpression e) {
		NodeType n = typeRestrictor.getRestrictedTypes().get(e);

		if (n != null) {
			if (n instanceof EqualsNode) {
				tlaModuleString.append("{");
				n.getExpression().apply(this);
				tlaModuleString.append("}");
			} else {
				n.getExpression().apply(this);
			}

		} else {
			tlaModuleString.append(typechecker.getType(e).getTlaType());
		}
	}

	private void printTypesOfIdentifierList(List<PExpression> copy) {
		if (copy.size() > 1) {
			tlaModuleString.append("(");
		}
		for (int i = 0; i < copy.size(); i++) {
			printTypeOfIdentifier(copy.get(i));

			if (i < copy.size() - 1)
				tlaModuleString.append(" \\times ");
		}
		if (copy.size() > 1) {
			tlaModuleString.append(")");
		}
	}

	@Override
	public void caseALambdaExpression(ALambdaExpression node) {
		/**
		 * B: %a,b.(P|e) TLA+ function: [<<a,b>> \in {<<a,b>> \in
		 * type(a)*type(b) : P}|e] relation: TLA+: {<< <<a,b>>, e>>: <<a,b>> \in
		 * {<<a,b>> \in type(a)*type(b): P}}
		 */
		inALambdaExpression(node);
		if (this.typechecker.getType(node) instanceof SetType) {
			tlaModuleString.append("{<<");
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getIdentifiers());
			printIdentifierList(copy);
			tlaModuleString.append(", ");
			node.getExpression().apply(this);
			tlaModuleString.append(">> : ");

			printIdentifierList(copy);

			tlaModuleString.append(" \\in { ");

			printIdentifierList(copy);

			tlaModuleString.append(" \\in ");
			printTypesOfIdentifierList(copy);
			tlaModuleString.append(" : ");
			node.getPredicate().apply(this);
			tlaModuleString.append("}");

			tlaModuleString.append("}");

		} else {
			tlaModuleString.append("[");
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getIdentifiers());
			printIdentifierList(copy);

			tlaModuleString.append(" \\in { ");
			printIdentifierList(copy);

			tlaModuleString.append(" \\in ");
			printTypesOfIdentifierList(copy);
			tlaModuleString.append(" : ");

			if (node.getPredicate() != null) {
				node.getPredicate().apply(this);
			}
			tlaModuleString.append("} |-> ");
			if (node.getExpression() != null) {
				node.getExpression().apply(this);
			}
			tlaModuleString.append("]");
		}
		outALambdaExpression(node);
	}

	@Override
	public void caseAFunctionExpression(AFunctionExpression node) {
		inAFunctionExpression(node);
		node.getIdentifier().apply(this);
		tlaModuleString.append("[");
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getParameters());
		for (int i = 0; i < copy.size(); i++) {
			if (i != 0) {
				tlaModuleString.append(", ");
			}
			copy.get(i).apply(this);
		}
		tlaModuleString.append("]");
		outAFunctionExpression(node);
	}

	@Override
	public void caseAPartialFunctionExpression(APartialFunctionExpression node) {
		inAPartialFunctionExpression(node);
		if (node.getLeft() != null) {
			node.getLeft().apply(this);
		}
		if (node.getRight() != null) {
			node.getRight().apply(this);
		}
		outAPartialFunctionExpression(node);
	}

	/**
	 * Sequences
	 */

	@Override
	public void caseASequenceExtensionExpression(
			ASequenceExtensionExpression node) {
		inASequenceExtensionExpression(node);
		tlaModuleString.append("<<");
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getExpression());
		for (int i = 0; i < copy.size(); i++) {
			copy.get(i).apply(this);
			if (i < copy.size() - 1)
				tlaModuleString.append(", ");
		}
		tlaModuleString.append(">>");
		outASequenceExtensionExpression(node);
	}

	/**
	 * Sets
	 */

	@Override
	public void caseASetExtensionExpression(ASetExtensionExpression node) {
		inASetExtensionExpression(node);
		tlaModuleString.append("{");
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getExpressions());
			for (int i = 0; i < copy.size(); i++) {
				if (i != 0) {
					tlaModuleString.append(", ");
				}
				copy.get(i).apply(this);
			}
		}
		tlaModuleString.append("}");
		outASetExtensionExpression(node);
	}

	@Override
	public void caseAEmptySetExpression(AEmptySetExpression node) {
		inAEmptySetExpression(node);
		tlaModuleString.append("{}");
		outAEmptySetExpression(node);
	}

	@Override
	public void caseAMemberPredicate(AMemberPredicate node) {
		inAMemberPredicate(node);
		node.getLeft().apply(this);
		tlaModuleString.append(" \\in ");
		node.getRight().apply(this);
		outAMemberPredicate(node);
	}

	@Override
	public void caseANotMemberPredicate(ANotMemberPredicate node) {
		inANotMemberPredicate(node);
		node.getLeft().apply(this);
		tlaModuleString.append(" \\notin ");
		node.getRight().apply(this);
		outANotMemberPredicate(node);
	}

	@Override
	public void caseAComprehensionSetExpression(AComprehensionSetExpression node) {
		inAComprehensionSetExpression(node);
		tlaModuleString.append("{");
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		printIdentifierList(copy);
		tlaModuleString.append(" \\in ");
		printTypesOfIdentifierList(copy);
		tlaModuleString.append(": ");
		if (node.getPredicates() != null) {
			node.getPredicates().apply(this);
		}
		tlaModuleString.append("}");
		outAComprehensionSetExpression(node);
	}

	@Override
	public void caseAUnionExpression(AUnionExpression node) {
		inAUnionExpression(node);
		node.getLeft().apply(this);
		tlaModuleString.append(" \\cup ");
		node.getRight().apply(this);
		outAUnionExpression(node);
	}

	@Override
	public void caseAIntersectionExpression(AIntersectionExpression node) {
		inAIntersectionExpression(node);
		node.getLeft().apply(this);
		tlaModuleString.append(" \\cap ");
		node.getRight().apply(this);
		outAIntersectionExpression(node);
	}

	@Override
	public void caseAPowSubsetExpression(APowSubsetExpression node) {
		inAPowSubsetExpression(node);
		tlaModuleString.append("SUBSET ");
		if (node.getExpression() != null) {
			node.getExpression().apply(this);
		}
		outAPowSubsetExpression(node);
	}

	@Override
	public void caseAPow1SubsetExpression(APow1SubsetExpression node) {
		inAPow1SubsetExpression(node);
		tlaModuleString.append("POW1(");
		if (node.getExpression() != null) {
			node.getExpression().apply(this);
		}
		tlaModuleString.append(")");
		outAPow1SubsetExpression(node);
	}

	@Override
	public void caseACardExpression(ACardExpression node) {
		inACardExpression(node);
		tlaModuleString.append("Cardinality(");
		node.getExpression().apply(this);
		tlaModuleString.append(")");
		outACardExpression(node);
	}

	@Override
	public void caseASubsetPredicate(ASubsetPredicate node) {
		inASubsetPredicate(node);
		node.getLeft().apply(this);
		tlaModuleString.append(" \\subseteq ");
		node.getRight().apply(this);
		outASubsetPredicate(node);
	}

	@Override
	public void caseASubsetStrictPredicate(ASubsetStrictPredicate node) {
		inASubsetStrictPredicate(node);
		node.getLeft().apply(this);
		tlaModuleString.append(" \\subset ");
		node.getRight().apply(this);
		outASubsetStrictPredicate(node);
	}

	@Override
	public void caseANotSubsetPredicate(ANotSubsetPredicate node) {
		inANotSubsetPredicate(node);
		tlaModuleString.append("notSubset(");
		node.getLeft().apply(this);
		tlaModuleString.append(", ");
		node.getRight().apply(this);
		tlaModuleString.append(")");
		outANotSubsetPredicate(node);
	}

	@Override
	public void caseANotSubsetStrictPredicate(ANotSubsetStrictPredicate node) {
		inANotSubsetStrictPredicate(node);
		tlaModuleString.append("notStrictSubset(");
		node.getLeft().apply(this);
		tlaModuleString.append(", ");
		node.getRight().apply(this);
		tlaModuleString.append(")");
		outANotSubsetStrictPredicate(node);
	}

	@Override
	public void caseAGeneralUnionExpression(AGeneralUnionExpression node) {
		inAGeneralUnionExpression(node);
		tlaModuleString.append("UNION ");
		node.getExpression().apply(this);
		outAGeneralUnionExpression(node);
	}

	@Override
	public void caseAGeneralIntersectionExpression(
			AGeneralIntersectionExpression node) {
		inAGeneralIntersectionExpression(node);
		tlaModuleString.append("inter(");
		node.getExpression().apply(this);
		tlaModuleString.append(")");
		outAGeneralIntersectionExpression(node);
	}

	/**
	 * Relations
	 */

	@Override
	public void caseACoupleExpression(ACoupleExpression node) {
		inACoupleExpression(node);
		List<PExpression> copy = new ArrayList<PExpression>(node.getList());
		for (int i = 0; i < copy.size() - 1; i++) {
			tlaModuleString.append("<<");
		}
		for (int i = 0; i < copy.size(); i++) {
			if (i != 0) {
				tlaModuleString.append(", ");
			}
			copy.get(i).apply(this);
			if (i != 0) {
				tlaModuleString.append(">>");
			}
		}
		outACoupleExpression(node);
	}

	@Override
	public void caseARelationsExpression(ARelationsExpression node) {
		inARelationsExpression(node);
		tlaModuleString.append("relation(");
		node.getLeft().apply(this);
		tlaModuleString.append(", ");
		node.getRight().apply(this);
		tlaModuleString.append(")");
		outARelationsExpression(node);
	}

	@Override
	public void caseADomainExpression(ADomainExpression node) {
		inADomainExpression(node);
		if (typechecker.getType(node.getExpression()) instanceof FunctionType) {
			tlaModuleString.append("DOMAIN ");
			node.getExpression().apply(this);
		} else {
			tlaModuleString.append("dom(");
			node.getExpression().apply(this);
			tlaModuleString.append(")");
		}
		outADomainExpression(node);
	}

	@Override
	public void caseARangeExpression(ARangeExpression node) {
		inARangeExpression(node);
		if (typechecker.getType(node.getExpression()) instanceof FunctionType) {
			tlaModuleString.append("ran(");

		} else {
			tlaModuleString.append("RANGE(");
		}
		node.getExpression().apply(this);
		tlaModuleString.append(")");
		outARangeExpression(node);
	}

	@Override
	public void caseAIdentityExpression(AIdentityExpression node) {
		inAIdentityExpression(node);
		tlaModuleString.append("id(");
		node.getExpression().apply(this);
		tlaModuleString.append(")");
		outAIdentityExpression(node);
	}

	@Override
	public void caseADomainRestrictionExpression(
			ADomainRestrictionExpression node) {
		inADomainRestrictionExpression(node);
		tlaModuleString.append("domain_restriction(");
		node.getLeft().apply(this);
		tlaModuleString.append(", ");
		node.getRight().apply(this);
		tlaModuleString.append(")");
		outADomainRestrictionExpression(node);
	}

	@Override
	public void caseADomainSubtractionExpression(
			ADomainSubtractionExpression node) {
		tlaModuleString.append("domain_substraction(");
		node.getLeft().apply(this);
		tlaModuleString.append(", ");
		node.getRight().apply(this);
		tlaModuleString.append(")");
	}

	/**
	 * Special Operator
	 */
	@Override
	public void caseAMinusOrSetSubtractExpression(
			AMinusOrSetSubtractExpression node) {
		inAMinusOrSetSubtractExpression(node);
		node.getLeft().apply(this);

		BType leftType = this.typechecker.getType(node.getLeft());
		if (leftType instanceof IntegerType) {
			tlaModuleString.append(" - ");
		} else {
			tlaModuleString.append(" \\ ");
		}

		node.getRight().apply(this);
		outAMinusOrSetSubtractExpression(node);
	}

	@Override
	public void caseAMultOrCartExpression(AMultOrCartExpression node) {
		inAMultOrCartExpression(node);
		node.getLeft().apply(this);

		BType leftType = this.typechecker.getType(node.getLeft());
		if (leftType instanceof IntegerType) {
			tlaModuleString.append(" * ");
		} else {
			tlaModuleString.append(" \\times ");
		}

		node.getRight().apply(this);
		outAMultOrCartExpression(node);
	}
}
