package edu.udel.cis.vsl.civl.model.common;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.abc.ast.entity.IF.Function;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.AssignsOrReadsNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.AssumesNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.BehaviorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.CallEventNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.CompositeEventNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ContractNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ContractNode.ContractKind;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.DependsEventNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.DependsEventNode.DependsEventNodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.DependsNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.EnsuresNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.GuardsNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPICollectiveBlockNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPIContractExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPIContractExpressionNode.MPIContractExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ReadOrWriteEventNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.RequiresNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ResultNode;
import edu.udel.cis.vsl.civl.model.IF.AbstractFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.model.IF.CIVLTypeFactory;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.contract.CallEvent;
import edu.udel.cis.vsl.civl.model.IF.contract.CompositeEvent.CompositeEventOperator;
import edu.udel.cis.vsl.civl.model.IF.contract.ContractFactory;
import edu.udel.cis.vsl.civl.model.IF.contract.DependsEvent;
import edu.udel.cis.vsl.civl.model.IF.contract.DependsEvent.DependsEventKind;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionBehavior;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionContract;
import edu.udel.cis.vsl.civl.model.IF.contract.NamedFunctionBehavior;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.Nothing;
import edu.udel.cis.vsl.civl.model.IF.expression.contracts.BehaviorBlock;
import edu.udel.cis.vsl.civl.model.IF.expression.contracts.ClauseSequence;
import edu.udel.cis.vsl.civl.model.IF.expression.contracts.ContractClause;
import edu.udel.cis.vsl.civl.model.IF.expression.contracts.ContractClause.ContractClauseKind;
import edu.udel.cis.vsl.civl.model.IF.expression.contracts.MPICollectiveBlockClause.COLLECTIVE_KIND;
import edu.udel.cis.vsl.civl.model.IF.expression.contracts.MemoryAccessClause;
import edu.udel.cis.vsl.civl.model.IF.expression.contracts.ObligationClause;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.model.common.contract.CommonContractFactory;
import edu.udel.cis.vsl.civl.util.IF.Pair;

public class ContractTranslator extends FunctionTranslator {
	/**
	 * The string type name of the Result Expression:<br>
	 * An special expression used to represent the result of a function in
	 * function contracts.
	 */
	public static final String contractResultName = "\\result";

	private CIVLFunction function;

	private ModelFactory modelFactory;

	private ModelBuilderWorker modelBuilder;

	private ContractFactory contractFactory = new CommonContractFactory();

	/******************** Constructor ********************/
	ContractTranslator(ModelBuilderWorker modelBuilder,
			ModelFactory modelFactory, CIVLTypeFactory typeFactory,
			CIVLFunction function) {
		super(modelBuilder, modelFactory, function);
		this.modelFactory = modelFactory;
		this.modelBuilder = modelBuilder;
		this.function = function;
	}

	public void translateFunctionContract(SequenceNode<ContractNode> contract) {
		FunctionContract result = contractFactory
				.newFunctionContract(modelFactory.sourceOf(contract));

		for (ContractNode clause : contract) {
			this.translateContractNodeNew(clause, result);
		}
		this.function.setFunctionContract(result);
	}

	private void translateContractNodeNew(ContractNode contractNode,
			FunctionContract functionContract) {
		this.translateContractNodeNewWork(contractNode, functionContract, null);
	}

	/**
	 * Translates a {@link ContractNode} to a {@link ContractClause}.
	 * 
	 * @param contractNode
	 * @return
	 */
	private void translateContractNodeNewWork(ContractNode contractNode,
			FunctionContract functionContract, NamedFunctionBehavior behavior) {
		CIVLSource source = modelFactory.sourceOf(contractNode);
		Scope scope = function.outerScope();
		FunctionBehavior functionBehavior = behavior != null ? behavior
				: functionContract.defaultBehavior();

		switch (contractNode.contractKind()) {
		case ENSURES: {
			Expression expression = translateExpressionNode(
					((EnsuresNode) contractNode).getExpression(), scope, true);
			functionBehavior.addPrecondition(expression);
			break;
		}
		case REQUIRES: {
			Expression expression = translateExpressionNode(
					((RequiresNode) contractNode).getExpression(), scope, true);
			functionBehavior.addPostcondition(expression);
			break;
		}
		case ASSIGNS_READS: {
			AssignsOrReadsNode assignsOrReads = (AssignsOrReadsNode) contractNode;
			boolean isAssigns = assignsOrReads.isAssigns();
			SequenceNode<ExpressionNode> muNodes = assignsOrReads
					.getMemoryList();

			for (ExpressionNode muNode : muNodes) {
				Expression mu = this.translateExpressionNode(muNode, scope,
						true);

				if (mu instanceof Nothing) {
					if (isAssigns) {
						if (functionBehavior.numAssignsMemoryUnits() == 0)
							functionBehavior.setAssingsNothing();
						else
							throw new CIVLSyntaxException(
									"assigns \\nothing conflicts with previous assigns clause",
									source);
					} else {
						if (functionBehavior.numAssignsMemoryUnits() == 0)
							functionBehavior.setReadsNothing();
						else
							throw new CIVLSyntaxException(
									"reads \\nothing conflicts with previous reads clause",
									source);
					}
				} else {
					if (isAssigns) {
						if (functionBehavior.assignsNothing())
							throw new CIVLSyntaxException(
									"assigns clause conflicts with previous assigns \\nothing",
									source);
						functionBehavior.addAssignsMemoryUnit(mu);
					} else {
						if (functionBehavior.readsNothing())
							throw new CIVLSyntaxException(
									"reads clause conflicts with previous reads \\nothing",
									source);
						functionBehavior.addReadsMemoryUnit(mu);
					}
				}
			}
			break;
		}
		case ASSUMES: {
			assert functionBehavior instanceof NamedFunctionBehavior;
			Expression expression = translateExpressionNode(
					((AssumesNode) contractNode).getPredicate(), scope, true);
			behavior.addAssumption(expression);
			break;
		}
		case BEHAVIOR: {
			assert behavior == null;
			BehaviorNode behaviorNode = (BehaviorNode) contractNode;
			NamedFunctionBehavior namedBehavior = this.contractFactory
					.newNamedFunctionBehavior(source, behaviorNode.getName()
							.name());
			SequenceNode<ContractNode> body = behaviorNode.getBody();

			for (ContractNode item : body) {
				this.translateContractNodeNewWork(item, null, namedBehavior);
			}
			functionContract.addNamedBehavior(namedBehavior);
			break;
		}

		case DEPENDS: {
			DependsNode dependsNode = (DependsNode) contractNode;
			SequenceNode<DependsEventNode> eventNodes = dependsNode
					.getEventList();

			for (DependsEventNode eventNode : eventNodes) {
				DependsEvent event = this.translateDependsEvent(eventNode,
						scope);

				if (event.dependsEventKind() == DependsEventKind.NOACT) {
					if (functionBehavior.numDependsEvents() > 0)
						throw new CIVLSyntaxException(
								"depends \\noact conflicts with previous depends clause",
								source);
					functionBehavior.setDependsNoact();
				} else if (event.dependsEventKind() == DependsEventKind.ANYACT) {
					if (functionBehavior.dependsNoact())
						throw new CIVLSyntaxException(
								"depends \\anyact conflicts with previous depends \\noact clause",
								source);
					functionBehavior.setDependsAnyact();
				} else
					functionBehavior.addDependsEvent(event);
			}
			if (functionBehavior.dependsAnyact())
				functionBehavior.clearDependsEvents();
			break;
		}
		case GUARDS: {
			Expression guard = this.translateExpressionNode(
					((GuardsNode) contractNode).getExpression(), scope, true);

			functionContract.setGuard(guard);
			break;
		}
		case PURE:
			functionContract.setPure(true);
			break;
		case COMPLETENESS:
		case MPI_COLLECTIVE:
		default:
			throw new CIVLUnimplementedFeatureException(
					"Translate Procedure ContractNode with "
							+ contractNode.contractKind());
		}
	}

	private DependsEvent translateDependsEvent(DependsEventNode eventNode,
			Scope scope) {
		DependsEventNodeKind kind = eventNode.getEventKind();
		CIVLSource source = this.modelFactory.sourceOf(eventNode);

		switch (kind) {
		case READ_WRITE: {
			ReadOrWriteEventNode readWriteEvent = (ReadOrWriteEventNode) eventNode;
			Set<Expression> muSet = new HashSet<>();
			SequenceNode<ExpressionNode> muNodeSet = readWriteEvent
					.getMemoryList();

			for (ExpressionNode muNode : muNodeSet) {
				muSet.add(this.translateExpressionNode(muNode, scope, true));
			}
			if (readWriteEvent.isRead())
				return this.contractFactory.newReadEvent(source, muSet);
			else
				return this.contractFactory.newWriteEvent(source, muSet);
		}
		case CALL: {
			CallEventNode callEvent = (CallEventNode) eventNode;
			Pair<Function, CIVLFunction> functionPair = this
					.getFunction(callEvent.getFunction());
			SequenceNode<ExpressionNode> argumentNodes = callEvent.arguments();
			List<Expression> arguments = new ArrayList<>();
			CallEvent call;

			for (ExpressionNode argNode : argumentNodes) {
				arguments.add(this
						.translateExpressionNode(argNode, scope, true));
			}
			call = this.contractFactory.newCallEvent(source,
					functionPair.right, arguments);
			if (functionPair.right == null)
				this.modelBuilder.callEvents.put(call, functionPair.left);
			return call;
		}
		case COMPOSITE: {
			CompositeEventNode compositeEvent = (CompositeEventNode) eventNode;
			CompositeEventOperator operator;
			DependsEvent left, right;

			switch (compositeEvent.eventOperator()) {
			case UNION:
				operator = CompositeEventOperator.UNION;
				break;
			case DIFFERENCE:
				operator = CompositeEventOperator.DIFFERENCE;
				break;
			case INTERSECT:
				operator = CompositeEventOperator.INTERSECT;
				break;
			default:
				throw new CIVLUnimplementedFeatureException(
						"unknown kind of composite event operatore: "
								+ compositeEvent.eventOperator(), source);
			}
			left = this.translateDependsEvent(compositeEvent.getLeft(), scope);
			right = this
					.translateDependsEvent(compositeEvent.getRight(), scope);
			return this.contractFactory.newCompositeEvent(source, operator,
					left, right);
		}
		case ANYACT:
			return this.contractFactory.newAnyactEvent(source);
		case NOACT:
			return this.contractFactory.newNoactEvent(source);
		default:
			throw new CIVLUnimplementedFeatureException(
					"unknown kind of depends event: " + kind, source);
		}

	}

	/**
	 * Translates a {@link ContractNode} to a {@link ContractClause}.
	 * 
	 * @param contractNode
	 * @return
	 */
	public ContractClause translateContractNode(ContractNode contractNode) {
		ExpressionNode expressionNode;
		Expression expression;
		CIVLSource nodeSource = modelFactory.sourceOf(contractNode);
		Scope scope = function.outerScope();

		// A processesGroup is associated to a contractNode, each time
		// processing a new contractNode, reset the global field of
		// processesGroup, ditto for contractCalls:
		switch (contractNode.contractKind()) {
		case ENSURES:
			expressionNode = ((EnsuresNode) contractNode).getExpression();
			expression = translateExpressionNode(expressionNode, scope, true);
			return modelFactory.obligationClause(ContractClauseKind.ENSURES,
					expression, scope, nodeSource);
		case REQUIRES:
			expressionNode = ((RequiresNode) contractNode).getExpression();
			expression = translateExpressionNode(expressionNode, scope, true);
			return modelFactory.obligationClause(ContractClauseKind.REQUIRES,
					expression, scope, nodeSource);
		case ASSIGNS_READS:
			return this.translateAssignsOrReadsNode(
					(AssignsOrReadsNode) contractNode, scope);
		case ASSUMES:
			expressionNode = ((AssumesNode) contractNode).getPredicate();
			expression = translateExpressionNode(expressionNode, scope, true);
			return modelFactory.obligationClause(ContractClauseKind.ASSUMES,
					expression, scope, nodeSource);
		case BEHAVIOR:
			return this.translateBehaviorBlock((BehaviorNode) contractNode,
					scope);
		case MPI_COLLECTIVE:
			return this.translateMPICollectiveBlock(
					(MPICollectiveBlockNode) contractNode, scope);
		case COMPLETENESS:
		case DEPENDS:
		case GUARDS:
		default:
			throw new CIVLUnimplementedFeatureException(
					"Translate Procedure ContractNode with "
							+ contractNode.contractKind());
		}
	}

	@Override
	protected Expression translateExpressionNode(ExpressionNode expressionNode,
			Scope scope, boolean translateConversions) {
		ExpressionKind kind = expressionNode.expressionKind();
		CIVLSource source = this.modelFactory.sourceOf(expressionNode);

		switch (kind) {
		case MPI_CONTRACT_EXPRESSION:
			return translateMPIContractExpression(
					(MPIContractExpressionNode) expressionNode, scope);
		case NOTHING: {
			return this.modelFactory.nothing(source);
		}
		case WILDCARD: {
			return this.modelFactory.wildcardExpression(
					source,
					this.translateABCType(source, scope,
							expressionNode.getConvertedType()));
		}
		default:
			return super.translateExpressionNode(expressionNode, scope,
					translateConversions);
		}
	}

	/**
	 * Translate a {@link MPIContractExpressionNode} into a CIVL Expression
	 * 
	 * @param node
	 * @param scope
	 * @return
	 */
	private Expression translateMPIContractExpression(
			MPIContractExpressionNode node, Scope scope) {
		MPIContractExpressionKind kind = node.MPIContractExpressionKind();
		switch (kind) {
		case MPI_INTEGER_CONSTANT:
		case MPI_EMPTY_IN:
		case MPI_EMPTY_OUT:
		case MPI_EQUALS:
		case MPI_REGION:
		case MPI_SIZE:
		}
		return null;

	}

	/**
	 * Translate an {@link MPICollectiveBlockNode} to a
	 * {@link MPICollectiveBlock}
	 * 
	 * @param node
	 *            The {@link MPICollectiveBlockNode}
	 * @param scope
	 *            The scope where the MPI collective block appears.
	 * @return
	 */
	private ContractClause translateMPICollectiveBlock(
			MPICollectiveBlockNode node, Scope scope) {
		Expression MPIComm;
		COLLECTIVE_KIND kind;
		ClauseSequence body;
		List<ContractClause> clauses = new LinkedList<>();
		Iterator<ContractNode> iterator = node.getBody().iterator();
		CIVLSource source = modelFactory.sourceOf(node);

		MPIComm = this.translateExpressionNode(node.getMPIComm(), scope, true);
		switch (node.getCollectiveKind()) {
		case P2P:
			kind = COLLECTIVE_KIND.P2P;
			break;
		case COL:
			kind = COLLECTIVE_KIND.COL;
			break;
		case BOTH:
			kind = COLLECTIVE_KIND.BOTH;
			break;
		default:
			throw new CIVLInternalException("Unreachable", source);
		}
		while (iterator.hasNext()) {
			ContractClause clause = translateContractNode(iterator.next());

			clauses.add(clause);
		}
		body = modelFactory.clauseSequence(clauses, scope,
				modelFactory.sourceOf(node.getBody().getSource()));
		return modelFactory.mpiCollectiveBlock(MPIComm, kind, body, scope,
				source);
	}

	/**
	 * Translate a {@link BehaviorNode} into a {@link BehaviorBlock}.
	 * 
	 * @param node
	 *            The {@link BehaviorNode}
	 * @param scope
	 *            The scope where the behavior block appers
	 * @return
	 */
	private ContractClause translateBehaviorBlock(BehaviorNode node, Scope scope) {
		SequenceNode<ContractNode> block = node.getBody();
		CIVLSource source = modelFactory.sourceOf(node);
		Expression assumption = modelFactory.trueExpression(source);
		ClauseSequence clauseSeq;
		List<ContractClause> clauses = new LinkedList<>();
		Iterator<ContractNode> blockIter = block.iterator();
		String name = node.getName().name();

		while (blockIter.hasNext()) {
			ContractNode subClause = blockIter.next();
			ContractClause translatedClause;

			translatedClause = this.translateContractNode(subClause);
			if (translatedClause.contractKind().equals(ContractKind.ASSUMES)) {
				Expression tmpAssum = ((ObligationClause) translatedClause)
						.getBody();
				CIVLSource spanSource = modelFactory.sourceOfSpan(node,
						subClause);

				assumption = modelFactory.binaryExpression(spanSource,
						BINARY_OPERATOR.AND, assumption, tmpAssum);
			} else
				clauses.add(translatedClause);
		}
		clauseSeq = modelFactory.clauseSequence(clauses, scope, source);
		return modelFactory.behaviorBlock(assumption, clauseSeq, name, scope,
				source);
	}

	/**
	 * Translate a {@link AssignsOrReadsNode} into a {@link MemoryAccessClause}
	 * 
	 * @param node
	 *            The {@link AssignsOrReadsNode}
	 * @param scope
	 *            The scope where the clause appears.
	 * @return
	 */
	private MemoryAccessClause translateAssignsOrReadsNode(
			AssignsOrReadsNode node, Scope scope) {
		Iterator<ExpressionNode> menLocIter = node.getMemoryList().iterator();
		List<Expression> memLocs = new LinkedList<>();
		Expression[] memLocArray;
		boolean isReads = node.isReads();
		CIVLSource source = modelFactory.sourceOf(node);

		while (menLocIter.hasNext()) {
			Expression memLoc = translateExpressionNode(menLocIter.next(),
					scope, true);

			memLocs.add(memLoc);
		}
		memLocArray = new Expression[memLocs.size()];
		return modelFactory.memoryAccessClause(memLocArray, isReads, scope,
				source);
	}

	/**
	 * Merging {@link ContractClause}s by calling the helper function:
	 * {@link #mergeSingleKindContracts(List, CIVLTypeFactory, ModelFactory)}.
	 * This function pre-processes contracts according to their
	 * {@link ContractClauseKind}, then calls the helper function.
	 * 
	 * @param contracts
	 *            The {@link List} of unmegred contracts
	 * @param typeFactory
	 *            A reference to a {@link CIVLTypeFactory} instance
	 * @param modelFactory
	 *            A reference to a {@link ModelFactory} instance
	 * @return
	 */
	// static public CIVLFunction mergeContracts(List<ContractClause> contracts,
	// CIVLTypeFactory typeFactory, ModelFactory modelFactory,
	// CIVLFunction function) {
	// List<ContractClause> requires, ensures;
	//
	// requires = new LinkedList<>();
	// ensures = new LinkedList<>();
	// for (ContractClause contract : contracts) {
	// ContractClauseKind kind = contract.contractKind();
	//
	// if (kind.equals(ContractClauseKind.REQUIRES))
	// requires.add(contract);
	// else if (kind.equals(ContractClauseKind.ENSURES))
	// ensures.add(contract);
	// else
	// throw new CIVLUnimplementedFeatureException(
	// "Merge contract with kind " + contract.contractKind());
	// }
	// for (ContractClause precond : mergeSingleKindContracts(requires,
	// typeFactory, modelFactory))
	// function.addPrecondition(precond);
	// for (ContractClause postcond : mergeSingleKindContracts(ensures,
	// typeFactory, modelFactory))
	// function.addPostcondition(postcond);
	// return function;
	// }

	/**
	 * Merging {@link ContractClause}s with same {@link ContractClauseKind}
	 * together according to following rules: <br>
	 * 1. collective contracts shouldn't be merged with non-collective
	 * contracts;<br>
	 * 
	 * 2. collective contracts should be merged according to their collective
	 * group;<br>
	 * 
	 * @param contracts
	 *            The {@link List} of unmegred contracts
	 * @param typeFactory
	 *            A reference to a {@link CIVLTypeFactory} instance
	 * @param modelFactory
	 *            A reference to a {@link ModelFactory} instance
	 * @return
	 */
	// static private List<ContractClause> mergeSingleKindContracts(
	// List<ContractClause> contracts, CIVLTypeFactory typeFactory,
	// ModelFactory modelFactory) {
	// Map<Variable, Integer> collectiveGroup = new HashMap<>();
	// ArrayList<ContractClause> collectiveContracts = new ArrayList<>();
	// ContractClause regularContracts = null;
	// CIVLType contractType = typeFactory.booleanType();
	//
	// for (ContractClause contract : contracts) {
	// ContractClauseKind kind = contract.contractKind();
	// CIVLSource contractBodySource = contract.getBody().getSource();
	// CIVLSource contractSource = contract.getSource();
	//
	// // Collective contracts should be merged with their groups:
	// if (contract.isCollectiveClause()) {
	// ContractClause canocContract;
	// int collectContractIdx;
	// VariableExpression group = (VariableExpression) contract
	// .getCollectiveGroup();
	//
	// if (!collectiveGroup.containsKey(group.variable())) {
	// collectContractIdx = collectiveContracts.size();
	// collectiveGroup.put(group.variable(), collectContractIdx);
	// canocContract = modelFactory.contractClauseExpression(
	// contract.getSource(), contractType, group,
	// contract.getBody(), kind);
	// collectiveContracts.add(canocContract);
	// } else {
	// Expression mergedBody;
	//
	// collectContractIdx = collectiveGroup.get(group.variable());
	// canocContract = collectiveContracts.get(collectContractIdx);
	// mergedBody = canocContract.getBody();
	// mergedBody = modelFactory
	// .binaryExpression(modelFactory.sourceOfSpan(
	// mergedBody.getSource(), contract.getBody()
	// .getSource()), BINARY_OPERATOR.AND,
	// mergedBody, contract.getBody());
	// canocContract = modelFactory.contractClauseExpression(
	// modelFactory.sourceOfSpan(
	// canocContract.getSource(), contractSource),
	// contractType, group, mergedBody, kind);
	// collectiveContracts.set(collectContractIdx, canocContract);
	// }
	// }
	// // Regular contracts should be merged together:
	// else {
	// Expression oldBody;
	//
	// if (regularContracts != null) {
	// oldBody = regularContracts.getBody();
	// oldBody = modelFactory.binaryExpression(modelFactory
	// .sourceOfSpan(oldBody.getSource(),
	// contractBodySource), BINARY_OPERATOR.AND,
	// oldBody, contract.getBody());
	// regularContracts = modelFactory.contractClauseExpression(
	// modelFactory.sourceOfSpan(
	// regularContracts.getSource(),
	// contractSource), contractType, null,
	// oldBody, kind);
	// } else
	// regularContracts = contract;
	// }
	// }
	// if (regularContracts != null)
	// collectiveContracts.add(regularContracts);
	// collectiveGroup.clear();
	// return collectiveContracts;
	// }

	@Override
	protected Expression translateFunctionCallExpression(
			FunctionCallNode callNode, Scope scope) {
		Expression result;
		ExpressionNode functionExpression = callNode.getFunction();
		Function callee;
		CIVLFunction civlFunction;
		String functionName;
		CIVLSource source = modelFactory.sourceOf(callNode);

		if (functionExpression instanceof IdentifierExpressionNode) {
			callee = (Function) ((IdentifierExpressionNode) functionExpression)
					.getIdentifier().getEntity();
		} else
			throw new CIVLUnimplementedFeatureException(
					"Function call must use identifier for now: "
							+ functionExpression.getSource());
		civlFunction = modelBuilder.functionMap.get(callee);
		functionName = civlFunction.name().name();
		assert civlFunction != null;
		if (civlFunction instanceof AbstractFunction) {
			List<Expression> arguments = new ArrayList<Expression>();

			for (int i = 0; i < callNode.getNumberOfArguments(); i++) {
				Expression actual = translateExpressionNode(
						callNode.getArgument(i), scope, true);

				actual = arrayToPointer(actual);
				arguments.add(actual);
			}
			result = modelFactory.abstractFunctionCallExpression(
					modelFactory.sourceOf(callNode),
					(AbstractFunction) civlFunction, arguments);
			return result;
		} else if (civlFunction.isSystemFunction()) {
			/*
			 * Following system functions can be used as expressions in
			 * contract:
			 */
			switch (functionName) {
			case "$mpi_isRecvBufEmpty":
			case "$mpi_isSendBufEmpty":
				return this.transformContractCall(civlFunction, scope,
						callNode, source);
			default:
			}
		}
		throw new CIVLUnimplementedFeatureException("Using function call: "
				+ functionName + "as expression in contract.");
	}

	/**
	 * Transform contract message buffer calls:
	 * 
	 * <code>collective(group) $mpi_isRecvBufEmpty(x) ==> $mpi_isRecvBufEmpty(x,
	 * group)</code> (ditto for other contract message buffer functions)
	 * 
	 * @param civlFunction
	 *            The {@link CIVLFunction} of the contract message buffer
	 *            function
	 * @param scope
	 *            The scope to where the contract message buffer belongs
	 * @param callNode
	 *            The {@link The FunctionCallNode} of the function call
	 * @param source
	 *            The CIVLSource of the function call
	 * @return
	 */
	private Expression transformContractCall(CIVLFunction civlFunction,
			Scope scope, FunctionCallNode callNode, CIVLSource source) {
		// A location only be used to construct a systemCallExpression,
		// it doesn't have income statements
		// and the outgoing statement dosen't have target:
		// Location floatingLocation;
		// List<Expression> arguments = new LinkedList<>();
		// Expression functionExpr = modelFactory.functionIdentifierExpression(
		// source, civlFunction);
		// Expression arg;
		// CallOrSpawnStatement civlSysFunctionCall;
		// SystemFunctionCallExpression result;
		// String functionName = civlFunction.name().name();
		//
		// floatingLocation = modelFactory.location(source, scope);
		// for (ExpressionNode argNode : callNode.getArguments()) {
		// argNode = callNode.getArgument(0);
		// arg = translateExpressionNode(argNode, scope, true);
		// arguments.add(arg);
		// }
		// // Add Collective Group as the second argument
		// assert processesGroup != null : "Building model for " + functionName
		// + "() but there is no collective group information";
		// arguments.add(processesGroup);
		// civlSysFunctionCall = modelFactory.callOrSpawnStatement(source,
		// floatingLocation, true, functionExpr, arguments,
		// modelFactory.trueExpression(null));
		// result =
		// modelFactory.systemFunctionCallExpression(civlSysFunctionCall);
		// return result;
		return null;
	}

	@Override
	protected Expression translateResultNode(ResultNode resultNode, Scope scope) {
		CIVLSource resultSource = modelFactory.sourceOf(resultNode);
		Variable resultVariable;
		Identifier resultIdentifier = modelFactory.identifier(resultSource,
				contractResultName);

		if (!scope.containsVariable(contractResultName)) {
			CIVLType resultType = this.translateABCType(resultSource, scope,
					resultNode.getType());

			resultVariable = modelFactory.variable(resultSource, resultType,
					resultIdentifier, scope.numVariables());
			scope.addVariable(resultVariable);
			resultVariable.setScope(scope);
		} else
			resultVariable = scope.variable(resultIdentifier);
		return modelFactory.variableExpression(resultSource, resultVariable);
	}
}
