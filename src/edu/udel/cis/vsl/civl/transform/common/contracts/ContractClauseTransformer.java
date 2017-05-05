package edu.udel.cis.vsl.civl.transform.common.contracts;

import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.PairNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPIContractExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPIContractExpressionNode.MPIContractExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.InitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CastNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.EnumerationConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.QuantifiedExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.RegularRangeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ResultNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.DeclarationListNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.ArrayTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode.TypeNodeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.Type.TypeKind;
import edu.udel.cis.vsl.abc.ast.value.IF.Value;
import edu.udel.cis.vsl.abc.ast.value.IF.ValueFactory.Answer;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.transform.common.BaseWorker;
import edu.udel.cis.vsl.civl.transform.common.contracts.FunctionContractBlock.ConditionalClauses;
import edu.udel.cis.vsl.civl.transform.common.contracts.MPIContractUtilities.TransformConfiguration;
import edu.udel.cis.vsl.civl.util.IF.Triple;
class ContractClauseTransformer {

	/**
	 * A collate-library function identifier:
	 */
	private final static String COLLATE_COMPLETE = "$collate_complete";

	/**
	 * A collate-library function identifier:
	 */
	private final static String COLLATE_ARRIVED = "$collate_arrived";

	/**
	 * A collate-library function identifier:
	 */
	private final static String COLLATE_GET_STATE = "$collate_get_state";

	/**
	 * A CIVL-MPI function identifier:
	 */
	private final static String MPI_SIZEOF = "sizeofDatatype";

	/**
	 * Generated old variable prefix:
	 */
	private final static String OLD_VAR_PREFIX = ContractTransformerWorker.CIVL_CONTRACT_PREFIX
			+ "_old_";

	/**
	 * Generated old variable counter:
	 */
	private int tmpOldCounter = 0;

	/**
	 * Generated heap variable prefix:
	 */
	private final static String HEAP_VAR_PREFIX = ContractTransformerWorker.CIVL_CONTRACT_PREFIX
			+ "_heap_";

	/**
	 * Generated heap variable counter:
	 */
	private int tmpHeapCounter = 0;

	/**
	 * Generated datatype-extent variable prefix:
	 */
	private final static String EXTENT_VAR_PREFIX = ContractTransformerWorker.CIVL_CONTRACT_PREFIX
			+ "_extent_";

	/**
	 * Generated datatype-extent variable counter:
	 */
	private int tmpExtentCounter = 0;

	/**
	 * Generated datatype-extent variable prefix:
	 */
	private final static String QUANT_VAR_PREFIX = ContractTransformerWorker.CIVL_CONTRACT_PREFIX
			+ "_quant_";

	/**
	 * Generated $mem type variable prefix:
	 */
	private final static String LAMB_VAR_PREFIX = ContractTransformerWorker.CIVL_CONTRACT_PREFIX
			+ "_lam_";

	/**
	 * Generated $mem type variable prefix:
	 */
	private final static String ASSIGN_VAR_PREFIX = ContractTransformerWorker.CIVL_CONTRACT_PREFIX
			+ "_a_";

	private int tmpAssignCounter = 0;

	/**
	 * Generated quantifier variable counter:
	 */
	private int tmpQuantCounter = 0;

	/**
	 * A reference to an instance of {@link NodeFactory}
	 */
	private NodeFactory nodeFactory;

	/**
	 * A reference to an instance of {@link ASTFactory}
	 */
	private ASTFactory astFactory;

	/**
	 * A reference to the owner of this class (contract transformer:
	 * {@link ContractTransformerWorker}):
	 */
	private ContractTransformerWorker contractTransformer;
	/**
	 * A set of entities of objects which have MPI_Datatype type. With such set
	 * maintained, it's able to be known that if a datatype was seen so that we
	 * can reduce the number of the generated intermediate variables:
	 */
	private Map<Entity, String> dataTypeEntity2Extentof;

	class TransformPair {
		List<BlockItemNode> requirements;
		List<BlockItemNode> ensurances;

		TransformPair(List<BlockItemNode> preNodes,
				List<BlockItemNode> postNodes) {
			this.requirements = preNodes;
			this.ensurances = postNodes;
		}
	}

	ContractClauseTransformer(ASTFactory astFactory,
			ContractTransformerWorker contractTransformer) {
		this.astFactory = astFactory;
		this.nodeFactory = astFactory.getNodeFactory();
		this.dataTypeEntity2Extentof = new HashMap<>();
		this.contractTransformer = contractTransformer;
	}

	/**
	 * Replace ACSL constructs to CIVL-C primitives
	 */
	void ACSLPrimitives2CIVLC(ExpressionNode predicate,
			TransformConfiguration config) throws SyntaxException {
		assert config.ignoreOld();
		old2ValueAt(predicate, null, config);
		result2intermediate(predicate, config);
	}

	void ACSLPrimitives2CIVLC(ExpressionNode predicate,
			ExpressionNode preCollateState, TransformConfiguration config)
			throws SyntaxException {
		ExpressionNode state = createCollateGetStateCall(preCollateState,
				predicate.getSource());

		old2ValueAt(predicate, state, config);
		result2intermediate(predicate, config);
	}

	TransformPair transformMPICollectiveBlock4Callee(
			FunctionContractBlock mpiBlock, TransformConfiguration config)
			throws SyntaxException {
		LinkedList<BlockItemNode> requirements = new LinkedList<>();
		LinkedList<BlockItemNode> ensurances = new LinkedList<>();
		ExpressionNode mpiComm = mpiBlock.getMPIComm();
		Source source = mpiComm.getSource();
		VariableDeclarationNode preStateDecl = createCollateStateInitializer(
				MPIContractUtilities.COLLATE_PRE_STATE, mpiComm);
		ExpressionNode preState = nodeFactory.newIdentifierExpressionNode(
				source,
				nodeFactory.newIdentifierNode(source, preStateDecl.getName()));
		VariableDeclarationNode postStateDecl = createCollateStateInitializer(
				MPIContractUtilities.COLLATE_POST_STATE, mpiComm);
		ExpressionNode postState = nodeFactory.newIdentifierExpressionNode(
				source,
				nodeFactory.newIdentifierNode(source, postStateDecl.getName()));

		requirements.add(preStateDecl);
		ensurances.add(postStateDecl);
		requirements.addAll(mpiConstantsInitialization(mpiComm));

		for (ConditionalClauses condClause : mpiBlock.getConditionalClauses()) {
			ExpressionNode requires = condClause.getRequires(nodeFactory);
			ExpressionNode ensures = condClause.getEnsures(nodeFactory);

			config.setIgnoreOld(true);
			config.setNoResult(true);
			ACSLPrimitives2CIVLC(requires, preState, config);
			requirements.addAll(transformClause2Checking(condClause.condition,
					requires, preState, condClause.getWaitsfors(), config));
			requirements.addAll(
					transformAssignsClause(condClause.getAssignsArgs()));
			config.setIgnoreOld(false);
			config.setNoResult(false);
			ACSLPrimitives2CIVLC(ensures, preState, config);
			ensurances.addAll(transformClause2Assumption(condClause.condition,
					ensures, postState, condClause.getWaitsfors(), config));
		}
		return new TransformPair(requirements, ensurances);
	}

	TransformPair transformMPICollectiveBlock4Target(
			FunctionContractBlock mpiBlock, TransformConfiguration config)
			throws SyntaxException {
		LinkedList<BlockItemNode> requirements = new LinkedList<>();
		LinkedList<BlockItemNode> ensurances = new LinkedList<>();
		ExpressionNode mpiComm = mpiBlock.getMPIComm();
		Source source = mpiComm.getSource();
		VariableDeclarationNode preStateDecl = createCollateStateInitializer(
				MPIContractUtilities.COLLATE_PRE_STATE, mpiComm);
		ExpressionNode preState = nodeFactory.newIdentifierExpressionNode(
				source,
				nodeFactory.newIdentifierNode(source, preStateDecl.getName()));
		VariableDeclarationNode postStateDecl = createCollateStateInitializer(
				MPIContractUtilities.COLLATE_POST_STATE, mpiComm);
		ExpressionNode postState = nodeFactory.newIdentifierExpressionNode(
				source,
				nodeFactory.newIdentifierNode(source, postStateDecl.getName()));

		requirements.addAll(mpiConstantsInitialization(mpiComm));
		config.setAlloc4Valid(true);
		for (ConditionalClauses condClause : mpiBlock.getConditionalClauses()) {
			ExpressionNode requires = condClause.getRequires(nodeFactory);

			requirements.addAll(allocation4Valids(requires, config));
		}
		config.setAlloc4Valid(false);
		requirements.add(preStateDecl);
		ensurances.add(postStateDecl);
		for (ConditionalClauses condClause : mpiBlock.getConditionalClauses()) {
			ExpressionNode requires = condClause.getRequires(nodeFactory);
			ExpressionNode ensures = condClause.getEnsures(nodeFactory);

			if (requires != null) {
				config.setIgnoreOld(true);
				config.setNoResult(true);
				ACSLPrimitives2CIVLC(requires, preState, config);
				requirements.addAll(transformClause2Assumption(
						condClause.condition, requires, preState,
						condClause.getWaitsfors(), config));
			}
			if (ensures != null) {
				// TODO: How check assigns ?
				config.setIgnoreOld(false);
				config.setNoResult(false);
				ACSLPrimitives2CIVLC(ensures, preState, config);
				ensurances.addAll(transformClause2Checking(condClause.condition,
						ensures, postState, condClause.getWaitsfors(), config));
			}
		}
		return new TransformPair(requirements, ensurances);
	}

	List<BlockItemNode> transformClause2Checking(ExpressionNode condition,
			ExpressionNode predicate, ExpressionNode collateState,
			List<ExpressionNode> arrivends, TransformConfiguration config)
			throws SyntaxException {
		StatementNode assertion = createAssertion(predicate.copy());

		assertion = MPIContractUtilities.withStatementWrapper(assertion,
				collateState, arrivends, config, nodeFactory);
		// conditional transformation:
		if (condition != null)
			assertion = nodeFactory.newIfNode(condition.getSource(),
					condition.copy(), assertion);

		List<BlockItemNode> results = new LinkedList<>();

		// elaborate waited arguments:
		if (arrivends != null)
			for (ExpressionNode arrivend : arrivends) {
				if (arrivend.expressionKind() == ExpressionKind.REGULAR_RANGE) {
					RegularRangeNode range = (RegularRangeNode) arrivend;

					results.add(createElaborateFor(range.getLow()));
					results.add(createElaborateFor(range.getHigh()));
				} else
					results.add(createElaborateFor(arrivend));
			}
		results.add(assertion);
		return results;
	}

	/**
	 * Transform a predicate specified by a contract clause into assumptions A.
	 * Each a in A is a condition that will be assumed hold. The returned set of
	 * {@link BlockItemNode} can be any kind of nodes serving such a assuming
	 * purpose, they can be declarations of temporary variables, CIVL-C $assume
	 * statements or assignments ( which is a direct way to assume some variable
	 * has some value), etc.
	 * 
	 * @param condition
	 *            The condition or assumption under where the predicate should
	 *            hold.
	 * @param predicate
	 *            The predicate expression
	 * @param evalKind
	 *            The {@link CollectiveEvaluationKind} for this predicate.
	 * @param collateState
	 *            The reference to a collate state, it's significant only when
	 *            the 'evalKind' is chosen
	 *            {@link CollectiveEvaluationKind#ARRIVED_WITH} or
	 *            {@link CollectiveEvaluationKind#COMPLETE_WITH}.
	 * @param arriveds
	 *            A set of places of processes, it's significant only when the
	 *            'evalKind' is chosen
	 *            {@link CollectiveEvaluationKind#ARRIVED_WITH}.
	 * @return
	 */
	List<BlockItemNode> transformClause2Assumption(ExpressionNode condition,
			ExpressionNode predicate, ExpressionNode collateState,
			List<ExpressionNode> arrivends, TransformConfiguration config) {
		StatementNode assumes = createAssumption(predicate.copy());

		assumes = MPIContractUtilities.withStatementWrapper(assumes,
				collateState, arrivends, config, nodeFactory);
		// conditional transformation:
		if (condition != null)
			assumes = nodeFactory.newIfNode(condition.getSource(),
					condition.copy(), assumes);

		List<BlockItemNode> results = new LinkedList<>();

		// elaborate waited process places:
		if (arrivends != null)
			for (ExpressionNode arrivend : arrivends) {
				if (arrivend.expressionKind() == ExpressionKind.REGULAR_RANGE) {
					RegularRangeNode range = (RegularRangeNode) arrivend;

					results.add(createElaborateFor(range.getLow()));
					results.add(createElaborateFor(range.getHigh()));
				} else
					results.add(createElaborateFor(arrivend));
			}
		results.add(assumes);
		return results;
	}

	// TODO: add check for sequential and mpi
	List<BlockItemNode> transformAssignsClause(List<ExpressionNode> memLocSets)
			throws SyntaxException {
		List<BlockItemNode> results = new LinkedList<>();

		for (ExpressionNode memoryLocationSet : memLocSets)
			results.add(refreshMemoryLocationSetExpression(memoryLocationSet));
		return results;
	}

	/*
	 * *************************************************************************
	 * Pre-processing Methods :
	 **************************************************************************/
	List<BlockItemNode> allocation4Valids(ExpressionNode expression,
			TransformConfiguration config) throws SyntaxException {
		ASTNode astNode = expression;
		List<OperatorNode> validNodes = new LinkedList<>();
		List<MPIContractExpressionNode> mpiValidNodes = new LinkedList<>();
		List<BlockItemNode> results = new LinkedList<>();

		do {
			if (astNode instanceof OperatorNode) {
				OperatorNode opNode = (OperatorNode) astNode;

				if (opNode.getOperator() == Operator.VALID)
					validNodes.add(opNode);
			} else if (astNode instanceof MPIContractExpressionNode) {
				MPIContractExpressionNode mpiPrimitive = (MPIContractExpressionNode) astNode;

				if (mpiPrimitive
						.MPIContractExpressionKind() == MPIContractExpressionKind.MPI_VALID)
					mpiValidNodes.add(mpiPrimitive);
			}
		} while ((astNode = astNode.nextDFS()) != null);
		if (!config.isInMPIBlock() && !mpiValidNodes.isEmpty())
			throw new CIVLSyntaxException(
					"\\mpi_valid shall not be used in sequential contracts",
					mpiValidNodes.get(0).getSource());
		if (config.alloc4Valid()) {
			for (OperatorNode validNode : validNodes)
				results.addAll(allocate4ACSLValid(validNode));
			for (MPIContractExpressionNode mpiValidNode : mpiValidNodes)
				results.addAll(allocate4MPIValid(mpiValidNode));

			// TODO: do forgot checking "extent > 0"
			/* Replace valid/mpi_valid expressions with simple true literal */
			substituteAllValid2True(expression);
		}
		return results;
	}

	/**
	 * Replace all appearances of {@link ResultNode} with an identifier
	 * expression "$result" for the given expression;
	 * 
	 * @param expression
	 * @return
	 */
	private ExpressionNode result2intermediate(ExpressionNode expression,
			TransformConfiguration config) {
		ASTNode visitor = expression;
		LinkedList<ASTNode> resultNodes = new LinkedList<>();

		assert expression.parent() == null;
		while (visitor != null) {
			if (visitor instanceof ResultNode)
				resultNodes.add(visitor);
			visitor = visitor.nextDFS();
		}
		if (config.noResult() && !resultNodes.isEmpty())
			throw new CIVLSyntaxException(
					"No \\result is allowed to be in 'requires' clauses",
					expression.getSource());
		while (!resultNodes.isEmpty()) {
			ASTNode result = resultNodes.removeLast();
			ASTNode parent = result.parent();
			int childIdx = result.childIndex();
			ExpressionNode artificialVar = nodeFactory
					.newIdentifierExpressionNode(result.getSource(),
							nodeFactory.newIdentifierNode(result.getSource(),
									MPIContractUtilities.ACSL_RESULT));

			if (parent == null) {
				// The given predicate is an instance of result expression:
				assert resultNodes.isEmpty();
				return artificialVar;
			}
			result.remove();
			parent.setChild(childIdx, artificialVar);
		}
		return expression;
	}

	/**
	 * Replace all OLD expressions with VALUE_AT expressions.
	 * 
	 * @param predicate
	 *            The predicate may contain OLD expressions.
	 * @param preState
	 *            The pre collate state
	 * @param config
	 * @return The predicate after substitution.
	 */
	private ExpressionNode old2ValueAt(ExpressionNode predicate,
			ExpressionNode preState, TransformConfiguration config) {
		ASTNode visitor = predicate;
		LinkedList<OperatorNode> oldExprs = new LinkedList<>();

		assert predicate.parent() == null;
		while (visitor != null) {
			if (visitor instanceof OperatorNode) {
				OperatorNode opNode = (OperatorNode) visitor;

				if (opNode.getOperator() == Operator.OLD)
					oldExprs.add(opNode);
			}
			visitor = visitor.nextDFS();
		}
		while (!oldExprs.isEmpty()) {
			OperatorNode old = oldExprs.removeLast();
			ASTNode parent = old.parent();
			int childIdx = old.childIndex();
			ExpressionNode value_at;

			old.getArgument(0).remove();
			value_at = nodeFactory.newValueAtNode(old.getSource(),
					preState.copy(),
					nodeFactory.newIdentifierExpressionNode(old.getSource(),
							nodeFactory.newIdentifierNode(old.getSource(),
									MPIContractUtilities.MPI_COMM_RANK_CONST)),
					old.getArgument(0));
			if (parent == null) {
				// The given predicate is an instance of old expression:
				assert oldExprs.isEmpty();
				return old;
			}
			old.remove();
			parent.setChild(childIdx, value_at);
		}
		return predicate;
	}

	/*
	 * *************************************************************************
	 * Methods creating new statements:
	 **************************************************************************/
	/**
	 * <p>
	 * <b>Summary: </b> Creates an assertion function call with an argument
	 * "predicate".
	 * </p>
	 * 
	 * @param predicate
	 *            The {@link ExpressionNode} which represents a predicate. It is
	 *            the only argument of an assertion call.
	 * @return A created assert call statement node;
	 */
	StatementNode createAssertion(ExpressionNode predicate) {
		ExpressionNode assertIdentifier = nodeFactory
				.newIdentifierExpressionNode(predicate.getSource(),
						nodeFactory.newIdentifierNode(predicate.getSource(),
								BaseWorker.ASSERT));
		FunctionCallNode assumeCall = nodeFactory.newFunctionCallNode(
				predicate.getSource(), assertIdentifier,
				Arrays.asList(predicate), null);
		return nodeFactory.newExpressionStatementNode(assumeCall);
	}

	/**
	 * <p>
	 * <b>Summary: </b> Creates an assumption function call with an argument
	 * "predicate".
	 * </p>
	 * 
	 * @param predicate
	 *            The {@link ExpressionNode} which represents a predicate. It is
	 *            the only argument of an assumption call.
	 * @return A created assumption call statement node;
	 */
	StatementNode createAssumption(ExpressionNode predicate) {
		ExpressionNode assumeIdentifier = identifierExpressionNode(
				predicate.getSource(), BaseWorker.ASSUME);
		FunctionCallNode assumeCall = nodeFactory.newFunctionCallNode(
				predicate.getSource(), assumeIdentifier,
				Arrays.asList(predicate), null);
		return nodeFactory.newExpressionStatementNode(assumeCall);
	}

	/**
	 * <p>
	 * Allocates for valid expressions.
	 * </p>
	 * 
	 * <p>
	 * Currently it only can deal with a fixed form:
	 * <code>\valid( ptr + integr-set)</code>, where
	 * <code>integr-set := regular_range (with default step)  
	 *                     | integer;
	 *                     
	 *       ptr must have type T* and T shall not be void;
	 * </code>
	 * </p>
	 * 
	 * @param valid
	 *            A valid expression
	 * @return A list of {@link BlockItemNode} express the allocation of the
	 *         valid expression.
	 * @throws SyntaxException
	 *             If the valid expression is not written in the canonical form.
	 */
	private List<BlockItemNode> allocate4ACSLValid(OperatorNode valid)
			throws SyntaxException {
		Source source = valid.getSource();
		ExpressionNode argument = valid.getArgument(0);
		ExpressionNode pointer, range = null;

		// Check if the argument of valid is in canonical form:
		if (argument instanceof OperatorNode) {
			OperatorNode opNode = (OperatorNode) argument;
			if (opNode.getOperator() != Operator.PLUS)
				throw new CIVLSyntaxException(
						"CIVL requires the argument of \\valid "
								+ "expression to be a canonical form:\n"
								+ "ptr (+ range)*\n"
								+ "range := integer-expression "
								+ "| integer-expression .. integer-expression",
						opNode.getSource());
			pointer = opNode.getArgument(0);
			range = opNode.getArgument(1);
			range = makeItRange(range);
		} else
			pointer = argument;

		assert pointer.getType().kind() == TypeKind.POINTER;
		PointerType ptrType = (PointerType) pointer.getType();
		ExpressionNode count;

		if (ptrType.referencedType().kind() == TypeKind.VOID)
			throw new CIVLSyntaxException(
					"Valid pointers asserted by \\valid expressions"
							+ " shall not have pointer-to-void type",
					pointer.getSource());

		if (range != null) {
			RegularRangeNode rangeNode = (RegularRangeNode) range;
			ExpressionNode high = rangeNode.getHigh();
			ExpressionNode low = rangeNode.getLow();
			Value constantVal = nodeFactory.getConstantValue(low);

			count = constantVal.isZero() == Answer.YES
					? high
					: nodeFactory.newOperatorNode(range.getSource(),
							Operator.MINUS, Arrays.asList(high, low));
		} else
			count = nodeFactory.newIntegerConstantNode(source, "1");

		Source ptrSource = pointer.getSource();
		TypeNode referedTypeNode;

		pointer = decast(pointer);
		referedTypeNode = BaseWorker.typeNode(ptrSource,
				ptrType.referencedType(), nodeFactory);

		// For \valid(ptr + x), there must equivalently be an array ptr[extent]
		// where extent >= x + 1:
		OperatorNode extent = nodeFactory.newOperatorNode(pointer.getSource(),
				Operator.PLUS, count.copy(), count = nodeFactory
						.newIntegerConstantNode(pointer.getSource(), "1"));

		return createAllocation(pointer, referedTypeNode, extent, ptrSource);
	}

	/**
	 * Allocates for \mpi_valid expressions.
	 * 
	 * @param condition
	 *            branch condition
	 * @param mpiValid
	 *            the \mpi_valid expression
	 * @param outputTriple
	 *            the output triple will be added with free statements
	 * @return
	 * @throws SyntaxException
	 */
	private List<BlockItemNode> allocate4MPIValid(
			MPIContractExpressionNode mpiValid) throws SyntaxException {
		Source source = mpiValid.getSource();
		ExpressionNode buf = mpiValid.getArgument(0);
		ExpressionNode count = mpiValid.getArgument(1);
		ExpressionNode datatype = mpiValid.getArgument(2);
		TypeNode typeNode;

		if (datatype instanceof EnumerationConstantNode) {
			EnumerationConstantNode mpiDatatypeConstant = (EnumerationConstantNode) datatype;
			String name = mpiDatatypeConstant.getName().name();
			String typedefname = "_" + name + "_t"; // quick translation

			typeNode = nodeFactory.newTypedefNameNode(nodeFactory
					.newIdentifierNode(datatype.getSource(), typedefname),
					null);
		} else {
			typeNode = nodeFactory.newBasicTypeNode(datatype.getSource(),
					BasicTypeKind.CHAR);
			// char data[count * extentof(datatype)];
			count = nodeFactory.newOperatorNode(source, Operator.TIMES, Arrays
					.asList(count.copy(), createMPIExtentofCall(datatype)));
		}
		return createAllocation(buf, typeNode, count, source);
	}

	/**
	 * @return a function call expression:
	 *         <code>$collate_get_state(colStateRef) </code>
	 */
	private ExpressionNode createCollateGetStateCall(ExpressionNode colStateRef,
			Source source) {
		return nodeFactory.newFunctionCallNode(source,
				identifierExpressionNode(source, COLLATE_GET_STATE),
				Arrays.asList(colStateRef.copy()), null);
	}

	/**
	 * @param a
	 *            function call expression: <code>$elaborate(expr)</code>
	 * @return
	 */
	private StatementNode createElaborateFor(ExpressionNode expression) {
		IdentifierExpressionNode funcIdent = nodeFactory
				.newIdentifierExpressionNode(expression.getSource(),
						nodeFactory.newIdentifierNode(expression.getSource(),
								BaseWorker.ELABORATE));
		ExpressionNode elaborateCall = nodeFactory.newFunctionCallNode(
				expression.getSource(), funcIdent,
				Arrays.asList(expression.copy()), null);

		return nodeFactory.newExpressionStatementNode(elaborateCall);
	}

	/**
	 * Create statements simulating allocation, i.e. declare an new artificial
	 * array variable then assign the reference to the given pointer.
	 * 
	 * @param pointer
	 *            A pointer expression p
	 * @param elementType
	 *            element type t
	 * @param numElements
	 *            number of elements n
	 * @param source
	 * @return A list of artifical {@link BlockItemNode}s
	 * @throws SyntaxException
	 */
	private List<BlockItemNode> createAllocation(ExpressionNode pointer,
			TypeNode elementType, ExpressionNode numElements, Source source)
			throws SyntaxException {
		List<BlockItemNode> artificials = new LinkedList<>();
		ExpressionNode extentGTzero = nodeFactory.newOperatorNode(source,
				Operator.LT, nodeFactory.newIntegerConstantNode(source, "0"),
				numElements.copy());
		TypeNode arrayType = nodeFactory.newArrayTypeNode(source, elementType,
				numElements);
		String allocationName = nextAllocationName();
		IdentifierNode allocationIdentifierNode;

		allocationIdentifierNode = nodeFactory
				.newIdentifierNode(pointer.getSource(), allocationName);

		VariableDeclarationNode artificialVariable = nodeFactory
				.newVariableDeclarationNode(source, allocationIdentifierNode,
						arrayType);
		// assign allocated object to pointer;
		ExpressionNode assign = nodeFactory.newOperatorNode(source,
				Operator.ASSIGN,
				Arrays.asList(pointer.copy(),
						nodeFactory.newIdentifierExpressionNode(source,
								allocationIdentifierNode.copy())));

		artificials.add(createAssumption(extentGTzero));
		artificials.add(artificialVariable);
		artificials.add(nodeFactory.newExpressionStatementNode(assign));
		return artificials;
	}

	/**
	 * 
	 * <p>
	 * <b>Summary: </b> Creates an $havoc_mem function call:
	 * </p>
	 * 
	 * @param var
	 * @return
	 */
	private ExpressionNode createHavocCall(ExpressionNode addr) {
		Source source = addr.getSource();
		ExpressionNode callIdentifier = identifierExpressionNode(source,
				ContractTransformerWorker.HAVOC);

		addr = nodeFactory.newOperatorNode(source, Operator.ADDRESSOF,
				Arrays.asList(addr));

		FunctionCallNode call = nodeFactory.newFunctionCallNode(source,
				callIdentifier, Arrays.asList(addr), null);

		return call;
	}

	/**
	 * create a call : <code>$mpi_sizeof(datatype)</code>
	 */
	private ExpressionNode createMPIExtentofCall(ExpressionNode datatype) {
		return nodeFactory.newFunctionCallNode(datatype.getSource(),
				identifierExpressionNode(datatype.getSource(),
						ContractTransformerWorker.MPI_EXTENTOF),
				Arrays.asList(datatype.copy()), null);
	}

	/**
	 * Create a temporary variable which represents the extent of an MPI data
	 * type.
	 * 
	 * @param datatype
	 * @param isMPIExtent
	 * @return
	 */
	private VariableDeclarationNode createMPIDatatypeVariable(
			ExpressionNode datatype, boolean isMPIExtent, String varName) {
		TypeNode intNode = nodeFactory.newBasicTypeNode(datatype.getSource(),
				BasicTypeKind.INT);
		ExpressionNode sizeofCall = nodeFactory.newFunctionCallNode(
				datatype.getSource(),
				identifierExpressionNode(datatype.getSource(), MPI_SIZEOF),
				Arrays.asList(datatype), null);

		return nodeFactory.newVariableDeclarationNode(datatype.getSource(),
				nodeFactory.newIdentifierNode(datatype.getSource(), varName),
				intNode, sizeofCall);
	}

	/**
	 * Given a valid expression v (either regular \valid or \mpi_valid), returns
	 * a boolean expression e which is equivalent to v that can be understood by
	 * CIVL
	 * 
	 * @param validNode
	 *            A valid expression
	 * @return A equivalent expression e to v that can be checked by CIVL
	 * @throws SyntaxException
	 */
	private ExpressionNode createValidCheckingCondition(
			ExpressionNode validNode) throws SyntaxException {
		Source source = validNode.getSource();
		ExpressionNode isDereferablePtr;

		// If it is a regular \valid
		if (validNode instanceof OperatorNode) {
			OperatorNode regValid = (OperatorNode) validNode;
			Triple<ExpressionNode, Operator, ExpressionNode> ptr_range = parseValidArgument(
					regValid.getArgument(0));

			regValid.remove();
			if (ptr_range.third != null)
				isDereferablePtr = createQualifiedPointerCheckingCondition(
						ptr_range.first, ptr_range.second, ptr_range.third);
			else
				isDereferablePtr = nodeFactory.newFunctionCallNode(
						regValid.getSource(),
						identifierExpressionNode(source, BaseWorker.DEREFRABLE),
						Arrays.asList(ptr_range.first.copy()), null);
		} else // else it is an \mpi_valid
		{
			// TODO: currently we can use the
			// system evaluation for \mpi_valid
			assert validNode instanceof MPIContractExpressionNode;
			isDereferablePtr = null;

		}
		return isDereferablePtr;
	}

	/**
	 * Given a pointer p, a Operator op (plus or minus) and a range r. Returns a
	 * expression e representing the condition that: for all int i; i in r,
	 * op(p, i) is a valid pointer. (Note that pointer that does plus or minus
	 * with an integer is still a pointer in C).
	 * 
	 * @param pointer
	 *            The base pointer
	 * @param plusOrMinus
	 *            The operator, PLUS or MINUS
	 * @param range
	 *            The range representing a set of offsets
	 * @return The quantified condition
	 */
	private ExpressionNode createQualifiedPointerCheckingCondition(
			ExpressionNode pointer, Operator plusOrMinus,
			ExpressionNode range) {
		ExpressionNode result;
		Source source = pointer.getSource();
		VariableDeclarationNode boundOffsetVar = nodeFactory
				.newVariableDeclarationNode(source,
						nodeFactory.newIdentifierNode(source, "i"), nodeFactory
								.newBasicTypeNode(source, BasicTypeKind.INT));
		OperatorNode ptrPLUSboundVar = nodeFactory.newOperatorNode(source,
				plusOrMinus, pointer.copy(),
				identifierExpressionNode(source, boundOffsetVar.getName()));
		List<PairNode<SequenceNode<VariableDeclarationNode>, ExpressionNode>> boundVars = new LinkedList<>();

		boundVars.add(nodeFactory.newPairNode(source,
				nodeFactory.newSequenceNode(source,
						"bound var declaration list",
						Arrays.asList(boundOffsetVar)),
				range.copy()));
		result = nodeFactory.newFunctionCallNode(source,
				identifierExpressionNode(source, BaseWorker.DEREFRABLE),
				Arrays.asList(ptrPLUSboundVar), null);
		result = nodeFactory.newQuantifiedExpressionNode(source,
				QuantifiedExpressionNode.Quantifier.FORALL,
				nodeFactory.newSequenceNode(source,
						"bound var declaration list", boundVars),
				null, result, null);
		return result;
	}

	/**
	 * Create an if-then statement by giving a condition expression c and a list
	 * l of {@link BlockItemNode}s: <code>
	 * if (c) {
	 *   l;
	 * }
	 * </code> If the given condition expression node is null, return l
	 * directly.
	 * 
	 * @param condition
	 *            An expression node representing the if-condition
	 * @param statements
	 *            A list of statements as the body of the if-then statement
	 * @param source
	 *            The {@link Source} related to the body statement.
	 * @return A list of {@link BlockItemNode} which represents an if-then
	 *         statement
	 */
	private List<BlockItemNode> createIfThemStmt(ExpressionNode condition,
			List<BlockItemNode> statements, Source source) {
		if (condition == null)
			return statements;
		else {
			StatementNode compundStatement = nodeFactory
					.newCompoundStatementNode(source, statements);

			compundStatement = nodeFactory.newIfNode(source, condition.copy(),
					compundStatement);
			return Arrays.asList(compundStatement);
		}
	}

	/*
	 * *************************************************************************
	 * Miscellaneous helper methods:
	 **************************************************************************/
	private List<BlockItemNode> mpiConstantsInitialization(
			ExpressionNode mpiComm) {
		List<BlockItemNode> results = new LinkedList<>();
		ExpressionNode rank = nodeFactory.newIdentifierExpressionNode(
				mpiComm.getSource(),
				nodeFactory.newIdentifierNode(mpiComm.getSource(),
						MPIContractUtilities.MPI_COMM_RANK_CONST));
		ExpressionNode size = nodeFactory.newIdentifierExpressionNode(
				mpiComm.getSource(),
				nodeFactory.newIdentifierNode(mpiComm.getSource(),
						MPIContractUtilities.MPI_COMM_SIZE_CONST));

		results.add(createMPICommRankCall(mpiComm.copy(), rank));
		results.add(createMPICommSizeCall(mpiComm.copy(), size));
		return results;
	}

	private StatementNode createMPICommRankCall(ExpressionNode mpiComm,
			ExpressionNode rankVar) {
		ExpressionNode callIdentifier = nodeFactory.newIdentifierExpressionNode(
				rankVar.getSource(),
				nodeFactory.newIdentifierNode(rankVar.getSource(),
						MPIContractUtilities.MPI_COMM_RANK_CALL));
		ExpressionNode addressOfRank = nodeFactory.newOperatorNode(
				rankVar.getSource(), Operator.ADDRESSOF, rankVar.copy());
		FunctionCallNode call = nodeFactory.newFunctionCallNode(
				rankVar.getSource(), callIdentifier,
				Arrays.asList(mpiComm.copy(), addressOfRank), null);
		return nodeFactory.newExpressionStatementNode(call);
	}

	private StatementNode createMPICommSizeCall(ExpressionNode mpiComm,
			ExpressionNode sizeVar) {
		ExpressionNode callIdentifier = nodeFactory.newIdentifierExpressionNode(
				sizeVar.getSource(),
				nodeFactory.newIdentifierNode(sizeVar.getSource(),
						MPIContractUtilities.MPI_COMM_SIZE_CALL));
		ExpressionNode addressOfSize = nodeFactory.newOperatorNode(
				sizeVar.getSource(), Operator.ADDRESSOF, sizeVar.copy());
		FunctionCallNode call = nodeFactory.newFunctionCallNode(
				sizeVar.getSource(), callIdentifier,
				Arrays.asList(mpiComm.copy(), addressOfSize), null);
		return nodeFactory.newExpressionStatementNode(call);
	}

	// TODO: doc
	private ExpressionNode mpiRegion2assign(
			MPIContractExpressionNode mpiRegion) {
		assert mpiRegion
				.MPIContractExpressionKind() == MPIContractExpressionKind.MPI_REGION;
		Source source = mpiRegion.getSource();
		ExpressionNode ptr = mpiRegion.getArgument(0);
		ExpressionNode count = mpiRegion.getArgument(1);
		ExpressionNode extent = mpiRegion.getArgument(2);
		ExpressionNode call = nodeFactory.newFunctionCallNode(source,
				identifierExpressionNode(source,
						ContractTransformerWorker.MPI_ASSIGNS),
				Arrays.asList(ptr.copy(), count.copy(), extent.copy()), null);

		return call;
	}

	/**
	 * Given an array type t, returns the weakest condition expression which
	 * implies that any array a of t, a is a valid array object. i.e. the extent
	 * of a greater than zero.
	 * 
	 * @param arrayTypeNode
	 *            An array type t.
	 * @return A condition e that e implies array of t is a valid array
	 * @throws SyntaxException
	 */
	private ExpressionNode validArrayTypeCondition(ArrayTypeNode arrayTypeNode)
			throws SyntaxException {
		TypeNode elementType = arrayTypeNode;
		ExpressionNode condition = null;
		ExpressionNode zero = nodeFactory
				.newIntegerConstantNode(arrayTypeNode.getSource(), "0");

		while (elementType.kind() == TypeNodeKind.ARRAY) {
			ArrayTypeNode arrayType = (ArrayTypeNode) elementType;
			ExpressionNode extent = arrayType.getExtent();

			if (extent != null) {
				ExpressionNode greaterThanZero = nodeFactory.newOperatorNode(
						extent.getSource(), Operator.LT, zero.copy(),
						extent.copy());

				if (condition == null)
					condition = greaterThanZero;
				else
					condition = nodeFactory.newOperatorNode(extent.getSource(),
							Operator.LAND, condition, greaterThanZero);
			}
			elementType = arrayType.getElementType();
		}
		return condition;
	}

	private VariableDeclarationNode createCollateStateInitializer(
			String collateStateName, ExpressionNode mpiComm) {
		Source source = mpiComm.getSource();
		InitializerNode initializer = createMPISnapshotCall(mpiComm.copy());
		TypeNode collateStateTypeName = nodeFactory
				.newTypedefNameNode(nodeFactory.newIdentifierNode(source,
						MPIContractUtilities.COLLATE_STATE_TYPE), null);
		IdentifierNode varIdent = nodeFactory.newIdentifierNode(source,
				collateStateName);

		return nodeFactory.newVariableDeclarationNode(source, varIdent,
				collateStateTypeName, initializer);
	}

	private ExpressionNode createMPISnapshotCall(ExpressionNode mpiComm) {
		Source source = mpiComm.getSource();
		ExpressionNode callIdentifier = nodeFactory.newIdentifierExpressionNode(
				source, nodeFactory.newIdentifierNode(source,
						MPIContractUtilities.MPI_SNAPSHOT));
		ExpressionNode hereNode = nodeFactory.newHereNode(source);
		FunctionCallNode call = nodeFactory.newFunctionCallNode(source,
				callIdentifier, Arrays.asList(mpiComm.copy(), hereNode), null);

		return call;
	}

	/**
	 * <p>
	 * Parse an argument expression of a valid expression into a triple: base
	 * address, PLUS/MINUS and range.
	 * </p>
	 * <p>
	 * Note that the argument of a valid expression can either be a single
	 * pointer type expression or a pointer PLUS/MINUS a range (or a singleton
	 * range which is an offset).
	 * </p>
	 * 
	 * @param arg
	 * @return
	 * @throws SyntaxException
	 */
	private Triple<ExpressionNode, Operator, ExpressionNode> parseValidArgument(
			ExpressionNode arg) throws SyntaxException {
		if (arg.expressionKind() == ExpressionKind.OPERATOR) {
			OperatorNode opNode = (OperatorNode) arg;

			assert opNode.getOperator() == Operator.PLUS
					|| opNode.getOperator() == Operator.MINUS;

			ExpressionNode left = opNode.getArgument(0);
			ExpressionNode right = opNode.getArgument(1);

			if (left.getConvertedType().kind() == TypeKind.POINTER)
				return new Triple<>(left, opNode.getOperator(), right);
			else
				return new Triple<>(right, opNode.getOperator(), left);

		} else
			return new Triple<>(arg, null, null);
	}

	/*
	 * *************************************************************************
	 * Methods give system generated entities names
	 **************************************************************************/

	/**
	 * @return a new name for intermediate variable used for transforming \old
	 *         expressions
	 */
	String nextOldValueName() {
		return OLD_VAR_PREFIX + tmpOldCounter++;
	}

	/**
	 * @return a new name for intermediate variable used for transforming
	 *         "extent of type" expressions. (e.g. $mpi_extent)
	 */
	String nextTypeExtentValueName() {
		return EXTENT_VAR_PREFIX + tmpExtentCounter++;
	}

	/**
	 * <p>
	 * This method requires caller to provide a counter as an argument so that
	 * the same names can be used in different name spaces. For lambda
	 * expressions, a whole expression is a name space.
	 * </p>
	 * 
	 * @param tmpLambCounter
	 *            The counter used to identify unique names
	 * @return a new name for intermediate variable used for transforming lambda
	 *         expressions
	 */
	String nextLambdaIdentifierName(int tmpLambCounter) {
		return LAMB_VAR_PREFIX + tmpLambCounter;
	}

	/**
	 * @return a new name for artificial variable used for transforming assigns
	 *         clauses
	 */
	private String nextAssignName() {
		return ASSIGN_VAR_PREFIX + tmpAssignCounter++;
	}

	/**
	 * @return a new name for artificial variable used for transforming
	 *         allocations
	 */
	private String nextAllocationName() {
		return HEAP_VAR_PREFIX + tmpHeapCounter++;
	}

	/*
	 * *************************************************************************
	 * Methods process ASSIGNS clauses
	 **************************************************************************/
	/**
	 * Process ACSL <b>assigns memory-location-set-list</b> clauses:
	 * 
	 * For callee functions, memory locations specified by <b>assigns</b> must
	 * be refreshed, i.e. assigned with fresh new symbolic constants.
	 */
	/**
	 * Assign fresh new symbolic constants to a memory locaton set expression.
	 * <p>
	 * A memory-location-set is
	 * <ol>
	 * <li>a set of l-values (including singleton set). According to ACSL
	 * reference v1.10 2.3.4, an expression representing a set of l-values can
	 * be formed with following rules (which are supported by CIVL):
	 * <ul>
	 * <li>set-&gtid := {x-&gtid | x in set}</li>
	 * <li>set.id := {x.id | x in set}</li>
	 * <li>*set := {*x | x in set}</li>
	 * <li>s1[s2] := { x1[x2] | x1 in s1, x2 in s2 }</li>
	 * <li><b>Base case:</b> t1 ... t2 := a set of integers in between [t1, t2]
	 * </li> Notice that there are two set expressions supported by CIVL but
	 * will never be able to express memory location set: &set and set1 + set2
	 * </ul>
	 * </li>
	 * <li>an MPI_REGION expression</li>
	 * </ol>
	 * </p>
	 * 
	 * <p>
	 * <b>For the expression e that represents a set of l-values, </b> this
	 * method returns a statement s for assigning fresh new symbolic constants
	 * to e: <br>
	 * <br>
	 * <code>
	 * s := $for(int i0 : r0)
	 *       $for(int i1 : r1)
	 *        ...
	 *         $for(int in : rn)
	 *           $havoc(addressof(e[i0/r0, i1/r1,...,in/rn]));     
	 * </code> where {r0,...rn} is the set R of base cases which consistitute e.
	 * </p>
	 * 
	 * <p>
	 * <b>For an MPI_REGION expression,</b> this method creates a call to the
	 * function<code>$mpi_assigns</code> which is defined in civl-mpi.cvl
	 * </p>
	 * 
	 * @param expression
	 *            An expression represents a memory location set
	 * @return A {@link BlockItemNode} which consists of statements that will
	 *         assign fresh new symbolic constants to the given expression
	 * @throws SyntaxException
	 *             When the given expression is not a valid memory location set
	 *             expression.
	 */
	private BlockItemNode refreshMemoryLocationSetExpression(
			ExpressionNode expression) throws SyntaxException {
		// if expression is an MPI_REGION expression:
		if (expression
				.expressionKind() == ExpressionKind.MPI_CONTRACT_EXPRESSION) {
			MPIContractExpressionNode mpiExpr = (MPIContractExpressionNode) expression;

			assert mpiExpr
					.MPIContractExpressionKind() == MPIContractExpressionKind.MPI_REGION;
			return nodeFactory
					.newExpressionStatementNode(mpiRegion2assign(mpiExpr));
		} else {
			Map<String, RegularRangeNode> baseCases = new HashMap<>();
			ExpressionNode havocee = processLvalueSetExpression(expression,
					baseCases);
			ExpressionNode havocCall = createHavocCall(havocee);
			StatementNode body = nodeFactory
					.newExpressionStatementNode(havocCall);
			TypeNode intTypeNode = nodeFactory.newBasicTypeNode(
					expression.getSource(), BasicTypeKind.INT);

			for (Entry<String, RegularRangeNode> entry : baseCases.entrySet()) {
				String loopIdentName = entry.getKey();
				RegularRangeNode range = entry.getValue();
				Source source = range.getSource();
				VariableDeclarationNode looIdentDecl = nodeFactory
						.newVariableDeclarationNode(source, nodeFactory
								.newIdentifierNode(source, loopIdentName),
								intTypeNode);
				DeclarationListNode declList = nodeFactory
						.newForLoopInitializerNode(source,
								Arrays.asList(looIdentDecl));

				body = nodeFactory.newCivlForNode(source, false, declList,
						range, body, null);
			}
			return body;
		}
	}

	/**
	 * <p>
	 * Given an expression e which represents an l-value set, this method will
	 * return <code>e[i0/r0, i1/r1,...,in/rn]</code> where {r0, r1, ...,rn} is
	 * the set of base cases (for base case, see
	 * {@link #refreshMemoryLocationSetExpression(ExpressionNode)}) constitute
	 * e, {i0, i1, ..., in} is a set of integer type identifiers.
	 * 
	 * </p>
	 * 
	 * @param lvalue
	 *            The given lvalue set expression
	 * @param baseCases
	 *            A map collection which will be added with a set of key-value
	 *            pairs (i, r) where i in {i0, i1, ..., in} and r is the
	 *            corresponding element in {r0, r1, ..., rn}
	 * @return
	 */
	private ExpressionNode processLvalueSetExpression(ExpressionNode lvalue,
			Map<String, RegularRangeNode> baseCases) {
		ExpressionNode copy = lvalue.copy();
		ASTNode node = copy;
		List<RegularRangeNode> ranges = new LinkedList<>();

		while (node != null) {
			if (node.nodeKind() == NodeKind.EXPRESSION
					&& ((ExpressionNode) node)
							.expressionKind() == ExpressionKind.REGULAR_RANGE) {
				ranges.add((RegularRangeNode) node);
			}
			node = node.nextDFS();
		}
		for (RegularRangeNode range : ranges) {
			String identifierName = nextAssignName();
			ExpressionNode identifierExpression = identifierExpressionNode(
					range.getSource(), identifierName);
			ASTNode parent = range.parent();
			int childIdx = range.childIndex();

			range.remove();
			parent.setChild(childIdx, identifierExpression);
			baseCases.put(identifierName, range);
		}
		return copy;
	}

	/**
	 * @param rangeOrInteger
	 *            Either an integer type expression or a regular range
	 *            expression.
	 * @return A regular range whose low and high are both equal to the given
	 *         expression 'rangeOrInteger' iff 'rangeOrInteger' is not a regular
	 *         range expression. Otherwise return 'rangeOrInteger' directly.
	 */
	private ExpressionNode makeItRange(ExpressionNode rangeOrInteger) {
		if (rangeOrInteger.getType().kind() == TypeKind.RANGE)
			return rangeOrInteger;
		assert rangeOrInteger.getType().kind() == TypeKind.BASIC;
		return nodeFactory.newRegularRangeNode(rangeOrInteger.getSource(),
				rangeOrInteger, rangeOrInteger);
	}

	/**
	 * If the given expression is a cast-expression: <code>(T) expr</code>,
	 * return an expression representing <code>expr</code>, otherwise no-op.
	 * 
	 * @param expression
	 *            An instance of {@link ExpressionNode}
	 * @return An expression who is the argument of a cast expression iff the
	 *         input is a cast expression, otherwise returns input itself.(i.e.
	 *         no-op).
	 */
	private ExpressionNode decast(ExpressionNode expression) {
		if (expression.expressionKind() == ExpressionKind.CAST) {
			CastNode castNode = (CastNode) expression;

			return castNode.getArgument();
		}
		return expression;
	}

	private void substituteAllValid2True(ExpressionNode predicate) {
		ASTNode visitor = predicate;
		List<ASTNode> valids = new LinkedList<>();

		while (visitor != null) {
			if (visitor instanceof OperatorNode) {
				OperatorNode opNode = (OperatorNode) visitor;

				if (opNode.getOperator() == Operator.VALID)
					valids.add(opNode);
			}
			if (visitor instanceof MPIContractExpressionNode) {
				MPIContractExpressionNode mpiPrimitiveNode = (MPIContractExpressionNode) visitor;

				if (mpiPrimitiveNode
						.MPIContractExpressionKind() == MPIContractExpressionKind.MPI_VALID)
					valids.add(mpiPrimitiveNode);
			}
			visitor = visitor.nextDFS();
		}
		for (ASTNode valid : valids) {
			ASTNode parent;
			int childIdx;
			ASTNode trueLiteral = nodeFactory
					.newBooleanConstantNode(valid.getSource(), true);

			parent = valid.parent();
			childIdx = valid.childIndex();
			parent.setChild(childIdx, trueLiteral);
		}
	}

	private IdentifierExpressionNode identifierExpressionNode(Source source,
			String name) {
		return nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, name));
	}
}
