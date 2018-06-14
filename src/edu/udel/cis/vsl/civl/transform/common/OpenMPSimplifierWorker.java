package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity.EntityKind;
import edu.udel.cis.vsl.abc.ast.entity.IF.Variable;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.AttributeKey;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpExecutableNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpForNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpParallelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpReductionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpReductionNode.OmpReductionOperator;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpSymbolReductionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpSyncNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpSyncNode.OmpSyncNodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpWorksharingNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpWorksharingNode.OmpWorksharingNodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.DeclarationListNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.IfNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ReturnNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.SwitchNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonDotNode;
import edu.udel.cis.vsl.abc.ast.util.ExpressionEvaluator;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.transform.IF.OpenMPSimplifier;

/**
 * This transformer analyzes OpenMP constructs and converts them to simpler,
 * i.e., less concurrent, instances of constructs.
 * 
 * This transform operates in two phases:
 * 
 * 1) Analyze OpenMP workshares to determine those that are provably
 * thread-independent, i.e., execution of workshares in parallel is guaranteed
 * to compute the same result.
 * 
 * 2) Transform OpenMP constructs based on the analysis results.
 * 
 * TBD: a) support nowait clauses b) support collapse clauses (confirm whether
 * collapse uses variables or the first "k" row indices) c) what is the
 * semantics of a parallel region with no pragma, i.e., do we have to reason
 * about its independence to remove the parallel pragma d) intra-iteration
 * dependences, e.g., x[i] = x[i] + a; e) critical, barrier, master, single and
 * other workshares f) calling sensitive parallel workshare nesting, i.e.,
 * caller has parallel pragma, callee has workshare g) semantics of nowait for
 * that continues to method return h) treatment of omp_ calls, i.e., should we
 * preserve the parallelism since the calls likely depend on it i) detect
 * non-escaping heap data from within a omp pragma context, e.g.,
 * fig4.98-threadprivate.c j) default private/shared when there are explicit
 * shared/private clauses that don't mention the var
 * 
 * 
 * @author dwyer
 * 
 */
public class OpenMPSimplifierWorker extends BaseWorker {

	// TBD: clean this up
	private AttributeKey dependenceKey;

	// Visitor identifies scalars through their "defining" declaration
	private Set<Entity> writeVars;
	private Set<Entity> readVars;
	private Set<OperatorNode> writeArrayRefs;
	private Set<OperatorNode> readArrayRefs;

	private Set<Entity> sharedWrites;
	private Set<Entity> sharedReads;
	private Set<OperatorNode> sharedArrayWrites;
	private Set<OperatorNode> sharedArrayReads;

	private Set<Entity> ompMethods;
	private Set<FunctionDefinitionNode> ompMethodDefinitions;

	/**
	 * A stack keeps track of locally declared entities during the traverse and
	 * analysis of an OMP parallel block (including nested ones).
	 */
	private Stack<Set<Entity>> locallyDeclaredEntities;

	private boolean allIndependent;

	private List<Entity> privateIDs;
	private List<Entity> loopPrivateIDs;

	private boolean debug = false;
	private CIVLConfiguration config;

	public OpenMPSimplifierWorker(ASTFactory astFactory,
			CIVLConfiguration config) {
		super(OpenMPSimplifier.LONG_NAME, astFactory);
		this.identifierPrefix = "$omp_sim_";
		this.config = config;
	}

	@Override
	public AST transform(AST unit) throws SyntaxException {
		if (config.ompNoSimplify())
			return unit;

		SequenceNode<BlockItemNode> rootNode = unit.getRootNode();

		assert this.astFactory == unit.getASTFactory();
		assert this.nodeFactory == astFactory.getNodeFactory();
		unit.release();

		// OpenMPParallelRegions ompRegions = new
		// OpenMPParallelRegions(rootNode);

		/*
		 * TBD: We want a proper inter-procedural analysis. This is more of a
		 * stop-gap.
		 * 
		 * There are two challenges: 1) Detect orphaning "omp parallel"
		 * statements - since they should not be simplified without considering
		 * whether the methods they call are themselves simplified 2) Detecting
		 * orphaned "omp" statements - since they should be analyzed for
		 * simplification even though they might not be lexically nested within
		 * an "omp parallel"
		 * 
		 * We collect the set of methods that contain an omp construct,
		 * recording their entities to detect calls to such methods for case 1)
		 * and recording their definition to drive analysis into those methods
		 * to handle case 2)
		 */
		ompMethods = new HashSet<Entity>();
		ompMethodDefinitions = new HashSet<FunctionDefinitionNode>();
		collectOmpMethods(rootNode);

		for (FunctionDefinitionNode fdn : ompMethodDefinitions) {
			transformOmp(fdn);
		}

		unit = astFactory.newAST(rootNode, unit.getSourceFiles(),
				unit.isWholeProgram());
		return unit;
	}

	AttributeKey getAttributeKey() {
		return this.dependenceKey;
	}

	private void addEntities(List<Entity> entityList,
			SequenceNode<IdentifierExpressionNode> clauseList) {
		if (clauseList != null) {
			for (IdentifierExpressionNode idExpression : clauseList) {
				Entity idEnt = idExpression.getIdentifier().getEntity();

				entityList.add(idEnt);
			}
		}
	}

	/*
	 * Scan program to collect methods involving omp constructs.
	 */
	private void collectOmpMethods(ASTNode node) {
		if (node instanceof FunctionDefinitionNode) {
			FunctionDefinitionNode fdn = (FunctionDefinitionNode) node;
			if (hasOmpConstruct(fdn.getBody())) {
				ompMethods.add(fdn.getEntity());
				ompMethodDefinitions.add(fdn);
			}
		} else if (node != null) {
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				collectOmpMethods(child);
			}
		}
	}

	private boolean callsMethodWithOmpConstruct(ASTNode node) {
		boolean result = false;
		if (node instanceof FunctionCallNode) {
			ExpressionNode fun = ((FunctionCallNode) node).getFunction();
			if (fun instanceof IdentifierExpressionNode) {
				result = ompMethods.contains(((IdentifierExpressionNode) fun)
						.getIdentifier().getEntity());
			}
		} else if (node != null) {
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				result = callsMethodWithOmpConstruct(child);
				if (result)
					break;
			}
		}
		return result;
	}

	/*
	 * Traverse the method declaration analyzing and simplifying omp constructs
	 */
	private void transformOmp(ASTNode node) {
		if (node instanceof OmpParallelNode) {
			OmpParallelNode opn = (OmpParallelNode) node;
			/*
			 * TBD: this code does not yet handle: - nested parallel blocks -
			 * sections workshares - collapse clauses - chunk clauses - omp_*
			 * calls which should be interpreted as being dependent
			 */

			/*
			 * Determine the private variables since they cannot generate
			 * dependences.
			 */
			privateIDs = new ArrayList<Entity>();
			addEntities(privateIDs, opn.privateList());
			addEntities(privateIDs, opn.copyinList());
			addEntities(privateIDs, opn.copyprivateList());
			addEntities(privateIDs, opn.firstprivateList());
			addEntities(privateIDs, opn.lastprivateList());
			SequenceNode<OmpReductionNode> reductionList = opn.reductionList();
			if (reductionList != null) {
				for (OmpReductionNode r : reductionList) {
					addEntities(privateIDs, r.variables());
				}
			}

			/*
			 * Initialize shared read/writes performed within parallel, but not
			 * in workshares
			 */
			sharedWrites = new HashSet<Entity>();
			sharedReads = new HashSet<Entity>();
			sharedArrayWrites = new HashSet<OperatorNode>();
			sharedArrayReads = new HashSet<OperatorNode>();
			locallyDeclaredEntities = new Stack<>();

			/*
			 * Analyze the workshares contained lexically within the parallel
			 * node. A parallel node is "orphaned" if it makes calls to methods
			 * that contain OpenMP statements or calls. An orphaned parallel
			 * should not be removed without determining if all called methods
			 * can be simplified to eliminate their OpenMP statements.
			 * 
			 * TBD: Currently the orphan analysis only checks a single level of
			 * call; the full solution would require construction of a call
			 * graph.
			 */
			allIndependent = true;

			// push an empty entry to the stack to keep track of locally
			// declared entities:
			locallyDeclaredEntities.push(new HashSet<>());
			// Visit the rest of this node
			transformOmpWorkshare(opn.statementNode());
			locallyDeclaredEntities.pop();
			/*
			 * Check for dependences between statements that are not within
			 * workshares
			 */
			for (Entity entity : sharedWrites) {
				// Currently I'm not sure if sharedWrites only contains
				// scalar variables, so I have to go over it. As long as one
				// scalar variable in it, there is possible a write-after-write
				// data race (modified and commented by Ziqing):
				if (entity.getEntityKind() == EntityKind.VARIABLE) {
					Variable var = (Variable) entity;

					if (var.getType().isScalar()) {
						allIndependent = false;
						break;
					}
				}
			}
			sharedWrites.retainAll(sharedReads);
			allIndependent &= sharedWrites.isEmpty();
			allIndependent &= noArrayRefDependences(sharedArrayWrites,
					sharedArrayReads);

			boolean isOrphaned = callsMethodWithOmpConstruct(
					opn.statementNode());

			if (allIndependent && !isOrphaned) {
				/*
				 * Remove the nested omp constructs, e.g., workshares, calls to
				 * omp_*, ordered sync nodes, etc.
				 */
				removeOmpConstruct(opn.statementNode());

				/*
				 * NB: the call above can change its argument (by restructuring
				 * the AST), so we need to recompute the statementNode below.
				 */

				// Remove "statement" node from "omp parallel" node
				StatementNode stmt = opn.statementNode();
				int stmtIndex = getChildIndex(opn, stmt);
				assert stmtIndex != -1;
				opn.removeChild(stmtIndex);

				// Link "statement" into the "omp parallel" parent
				ASTNode parent = opn.parent();
				int parentIndex = getChildIndex(parent, opn);
				assert parentIndex != -1;
				parent.setChild(parentIndex, stmt);
			}
		} else if (node instanceof OmpExecutableNode) {
			privateIDs = new ArrayList<Entity>();

			transformOmpWorkshare(node);

		} else if (node != null) {
			// BUG: can get here with null values in parallelfor.c example

			/*
			 * Could match other types here that have no ForLoopNode below them
			 * and skip their traversal to speed things up.
			 */
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				transformOmp(child);
			}
		}
	}

	/*
	 * This method assumes that all of the OMP statements that are encountered
	 * can be safely removed or transformed into non-OMP equivalents.
	 */
	private void removeOmpConstruct(ASTNode node) {
		if (node instanceof OmpExecutableNode) {
			// Remove "statement" node from "omp statement" node
			StatementNode stmt = ((OmpExecutableNode) node).statementNode();
			int stmtIndex = getChildIndex(node, stmt);
			assert stmtIndex != -1;
			node.removeChild(stmtIndex);

			// Link "statement" into the "omp workshare" parent
			ASTNode parent = node.parent();
			int parentIndex = getChildIndex(parent, node);
			assert parentIndex != -1;

			parent.setChild(parentIndex, stmt);
			removeOmpConstruct(stmt);

		} else if (node instanceof FunctionCallNode
				&& ((FunctionCallNode) node)
						.getFunction() instanceof IdentifierExpressionNode
				&& ((IdentifierExpressionNode) ((FunctionCallNode) node)
						.getFunction()).getIdentifier().name()
								.startsWith("omp_")) {
			// I replace node with a null-like node.
			Source nodeSource = node.getSource();
			String ompFunctionName = ((IdentifierExpressionNode) ((FunctionCallNode) node)
					.getFunction()).getIdentifier().name();
			ASTNode replacement = null;
			if (ompFunctionName.equals("omp_get_thread_num")) {
				replacement = nodeFactory.newIntConstantNode(nodeSource, 0);
			} else if (ompFunctionName.equals("omp_get_num_threads")
					|| ompFunctionName.equals("omp_get_max_threads")
					|| ompFunctionName.equals("omp_get_num_procs")
					|| ompFunctionName.equals("omp_get_thread_limit")) {
				replacement = nodeFactory.newIntConstantNode(nodeSource, 1);
			} else if (ompFunctionName.equals("omp_init_lock")
					|| ompFunctionName.equals("omp_set_lock")
					|| ompFunctionName.equals("omp_unset_lock")
					|| ompFunctionName.equals("omp_set_num_threads")) {
				// delete this node
				replacement = nodeFactory.newCastNode(nodeSource,
						nodeFactory.newVoidTypeNode(nodeSource),
						nodeFactory.newIntConstantNode(nodeSource, 0));
			} else if (ompFunctionName.equals("omp_get_wtime")) {
				// this will be transformed by the OMP transformer

			} else {
				assert false : "Unsupported omp function call "
						+ ompFunctionName
						+ " cannot be replaced by OpenMP simplifier";
			}

			// Link "replacement" into the omp call's parent
			ASTNode parent = node.parent();
			int parentIndex = getChildIndex(parent, node);
			assert parentIndex != -1;
			parent.setChild(parentIndex, replacement);
		} else if (node != null) {
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				removeOmpConstruct(child);
			}
		}
	}

	/*
	 * Scan workshares to drive dependence analysis.
	 */
	private void transformOmpWorkshare(ASTNode node) {
		if (node instanceof OmpForNode) {
			OmpForNode ompFor = (OmpForNode) node;
			/*
			 * Determine the private variables since they cannot generate
			 * dependences.
			 * 
			 * TBD: Factor this out to a method and pass it as a parameter to
			 * processFor
			 */
			loopPrivateIDs = new ArrayList<Entity>();
			addEntities(loopPrivateIDs, ompFor.privateList());
			addEntities(loopPrivateIDs, ompFor.copyinList());
			addEntities(loopPrivateIDs, ompFor.copyprivateList());
			addEntities(loopPrivateIDs, ompFor.firstprivateList());
			addEntities(loopPrivateIDs, ompFor.lastprivateList());
			SequenceNode<OmpReductionNode> reductionList = ompFor
					.reductionList();
			if (reductionList != null) {
				for (OmpReductionNode r : reductionList) {
					addEntities(loopPrivateIDs, r.variables());
				}
			}

			processFor(ompFor);

			// reset variable to avoid interference with processing of non-loop
			// parallel regions
			loopPrivateIDs = new ArrayList<Entity>();

		} else if (node instanceof OmpSyncNode) {
			OmpSyncNode syncNode = (OmpSyncNode) node;

			OmpSyncNodeKind kind = syncNode.ompSyncNodeKind();
			switch (kind) {
				case MASTER :
					allIndependent = false;
					break;
				case CRITICAL :
					allIndependent = false;
					break;
				case BARRIER :
					allIndependent = false;;
					break;
				case ORDERED :
					/*
					 * Should be able to optimize this case since semantics
					 * guarantee serial order
					 */
					allIndependent = false;;
					break;
				case FLUSH :
					allIndependent = false;;
					break;
				default :
					allIndependent = false;
					break;
			}

		} else if (node instanceof OmpWorksharingNode) {
			OmpWorksharingNode wsNode = (OmpWorksharingNode) node;

			OmpWorksharingNodeKind kind = wsNode.ompWorkshareNodeKind();
			switch (kind) {
				case SECTIONS :
					allIndependent = false;
					break;
				case SECTION :
					allIndependent = false;
					break;
				case SINGLE :
					allIndependent = false;
					break;
				default :
					allIndependent = false;
					break;
			}

		} else if (isAssignment(node)) {
			/*
			 * Collect up the set of assignment statements that are not within
			 * workshares
			 */

			/*
			 * This code is clunky because it uses globals, but we can
			 * accumulate the read/write sets for these statements within the
			 * parallel and then post process them.
			 */

			// Reset visitor globals
			writeVars = new HashSet<Entity>();
			readVars = new HashSet<Entity>();
			writeArrayRefs = new HashSet<OperatorNode>();
			readArrayRefs = new HashSet<OperatorNode>();

			loopPrivateIDs = new ArrayList<Entity>();

			collectAssignRefExprs(node);

			if (debug) {
				System.out.println(
						"Analyzed non-workshare assignment " + node + " with:");
				System.out.println("   sharedReads = " + readVars);
				System.out.println("   sharedWrites = " + writeVars);
				System.out.println("   sharedArrayReads = " + readArrayRefs);
				System.out.println("   sharedArrayWrites = " + writeArrayRefs);
			}

			sharedReads.addAll(readVars);
			sharedWrites.addAll(writeVars);
			sharedArrayReads.addAll(readArrayRefs);
			sharedArrayWrites.addAll(writeArrayRefs);

			/*
			 * TBD: we are not collecting the reads from all of the appropriate
			 * statements. For example the reads in the conditions of
			 * if/while/for/...
			 */

		} else if (node != null) {

			// BUG: can get here with null values in parallelfor.c example

			/*
			 * Could match other types here that have no ForLoopNode below them
			 * and skip their traversal to speed things up.
			 */
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				transformOmpWorkshare(child);
			}
		}
	}

	/*
	 */
	private void processFor(OmpForNode ompFor) {
		ForLoopNode fln = (ForLoopNode) ompFor.statementNode();

		/*
		 * If the "omp for" has a "nowait" clause then it can still be
		 * transformed as long as its parent is the "omp parallel", i.e., no
		 * additional statements follow it in the "omp parallel"
		 */
		if (ompFor.nowait()) {
			if (!(ompFor.parent() instanceof OmpParallelNode))
				return;
		}

		/*
		 * Need to handle collapse through the use of a sequence of iteration
		 * variables and associated constraints on them.
		 */

		/*
		 * The following block computes the loop appropriate constraints that
		 * bound the loop variable's range.
		 * 
		 * This code handles non-normalized loops, e.g., starting at non-zero
		 * indices, iterating down or up, etc.
		 * 
		 * TBD: record the increment to be used for more precise dependence
		 * constraints.
		 * 
		 * It does not check whether those bounding expressions are loop
		 * invariant, which is required by the OpenMP standard, but it does
		 * enforce a number of other canonical loop form constraints.
		 */
		IdentifierNode loopVariable = null;
		ExpressionNode initBound = null;

		List<ExpressionNode> boundingConditions = new LinkedList<ExpressionNode>();

		{
			ForLoopInitializerNode initializer = fln.getInitializer();
			if (initializer instanceof OperatorNode) {
				OperatorNode assign = (OperatorNode) initializer;
				Operator op = assign.getOperator();
				if (op == Operator.ASSIGN) {
					ExpressionNode left = assign.getArgument(0);
					assert left instanceof IdentifierExpressionNode : "OpenMP Canonical Loop Form violated (identifier required on LHS of initializer)";
					loopVariable = ((IdentifierExpressionNode) left)
							.getIdentifier().copy();
					initBound = assign.getArgument(1).copy();
				} else {
					assert false : "OpenMP Canonical Loop Form violated (initializer must be an assignment) :"
							+ assign;
				}

			} else if (initializer instanceof DeclarationListNode) {
				if (initializer instanceof SequenceNode<?>) {
					@SuppressWarnings("unchecked")
					SequenceNode<VariableDeclarationNode> decls = (SequenceNode<VariableDeclarationNode>) initializer;
					Iterator<VariableDeclarationNode> it = (Iterator<VariableDeclarationNode>) decls
							.iterator();
					VariableDeclarationNode vdn = it.next();
					if (it.hasNext()) {
						assert false : "OpenMP Canonical Loop Form violated (single initializer only) :"
								+ initializer;
					}

					loopVariable = vdn.getEntity().getDefinition()
							.getIdentifier().copy();

					assert vdn
							.getInitializer() instanceof ExpressionNode : "OpenMP Canonical Loop Form violated (initializer must be simple expression)";

					// Record the initializer expression to build up the
					// initCondition below
					initBound = (ExpressionNode) vdn.getInitializer().copy();
				} else {
					assert false : "Expected SequenceNode<VariableDeclarationNode>: "
							+ initializer;
				}

			} else {
				assert false : "Expected OperatorNode or DeclarationListNode: "
						+ initializer;
			}

			ExpressionNode condition = fln.getCondition();

			if (condition instanceof OperatorNode) {
				OperatorNode relop = (OperatorNode) condition;

				/*
				 * The initial bound of the iteration space is established by an
				 * assignment statement. We need to convert that assignment into
				 * an appropriate inequality to appropriately constrain the loop
				 * variable values. The code assumes that the polarity of the
				 * loop exit condition and the increment operator are
				 * compatible, i.e., a "<" or "<=" test is coupled with an "++"
				 * and a ">" or ">=" with a "--"; this condition is not checked
				 * here. We reverse the polarity of the loop exit condition to
				 * establish the boundary condition associated with the
				 * initialization and make that condition non-strict to account
				 * for the equality implicit in the assignment.
				 * 
				 * This results in the following types of behavior: for (int
				 * i=0; i<N; i++) generates "i>=0" as an "initial" bound for
				 * (int i=0; i<=N-1; i++) generates "i>=0" as an "initial" bound
				 * for (int i=N-1; i>=0; i++) generates "i<=N-1" as an "initial"
				 * bound for (int i=N-1; i>-1; i++) generates "i<=N-1" as an
				 * "initial" bound
				 */
				List<ExpressionNode> arguments = new LinkedList<ExpressionNode>();
				ExpressionNode lvNode = nodeFactory.newIdentifierExpressionNode(
						ompFor.getSource(), loopVariable);
				arguments.add(lvNode);
				arguments.add(initBound);

				Operator op = relop.getOperator();
				if (op == Operator.LT || op == Operator.LTE) {
					OperatorNode newBoundExpr = nodeFactory.newOperatorNode(
							ompFor.getSource(), Operator.GTE, arguments);
					boundingConditions.add(newBoundExpr);

				} else if (op == Operator.GT || op == Operator.GTE) {
					OperatorNode newBoundExpr = nodeFactory.newOperatorNode(
							ompFor.getSource(), Operator.LTE, arguments);
					boundingConditions.add(newBoundExpr);
				} else {
					assert false : "OpenMP Canonical Loop Form violated (condition must be one of >, >=, <, or <=) :"
							+ relop;
				}

				ExpressionNode left = relop.getArgument(0);
				ExpressionNode right = relop.getArgument(1);

				/*
				 * variable must be either left or right, but not both
				 * 
				 * Currently these checks are based on the name of the variable.
				 * Perhaps it is better to use the symbol information, i.e.,
				 * getEntity()
				 */
				int loopVariableCount = 0;
				if (left instanceof IdentifierExpressionNode) {
					IdentifierNode id = ((IdentifierExpressionNode) left)
							.getIdentifier();
					if (id.name().equals(loopVariable.name())) {
						loopVariableCount++;
					}
				}

				if (right instanceof IdentifierExpressionNode) {
					IdentifierNode id = ((IdentifierExpressionNode) right)
							.getIdentifier();
					if (id.name().equals(loopVariable.name())) {
						loopVariableCount++;
					}
				}

				if (loopVariableCount == 1) {
					boundingConditions.add(condition);
				} else {
					assert false : "OpenMP Canonical Loop Form violated (requires variable condition operand) :"
							+ condition;
				}
			} else {
				assert false : "OpenMP Canonical Loop Form violated (condition malformed) :"
						+ condition;
			}

		}

		/*
		 * Accumulate the set of memory-referencing expressions, i.e., variable
		 * references, array index expressions, on the LHS and the RHS.
		 * 
		 * TBD: Need to generalize this to record the full alias-equivalence
		 * relation. - parameters of the same type are potential aliases unless
		 * the "restrict" keyword is used - assignments through pointers need to
		 * be handled as well
		 * 
		 * TBD: We need to know the dimensions of array parameters or else we
		 * cannot reason about independent memory regions, e.g., indexing of the
		 * end of one array may touch an element of an adjacent array.
		 */
		StatementNode body = fln.getBody();
		writeVars = new HashSet<Entity>();
		readVars = new HashSet<Entity>();
		writeArrayRefs = new HashSet<OperatorNode>();
		readArrayRefs = new HashSet<OperatorNode>();

		collectAssignRefExprs(body);

		/*
		 * Check for name-based dependences
		 */
		boolean independent = true;
		// For each entity in writeVars, if it is not in the local-declaration
		// collection, add it to sharedWrites (modified by Ziqing):
		for (Entity entity : writeVars) {
			if (!locallyDeclaredEntities.contains(entity)) {
				sharedWrites.add(entity);
				if (entity.getEntityKind() == EntityKind.VARIABLE)
					if (((Variable) entity).getType().isScalar()) {
						independent = false;
						break;
					}
			}
		}

		writeVars.retainAll(readVars);
		independent &= writeVars.isEmpty();

		/*
		 * Check for array-based dependences.
		 */

		independent &= noArrayRefDependences(boundingConditions, writeArrayRefs,
				readArrayRefs);

		if (debug) {
			System.out.println(
					"Found " + (independent ? "independent" : "dependent")
							+ " OpenMP for " + ompFor);
			System.out.println("  writeVars : " + writeVars);
			System.out.println("  readVars : " + readVars);
			System.out.println("  writeArrays : " + writeArrayRefs);
			System.out.println("  readArrays : " + readArrayRefs);
		}

		if (independent) {
			/*
			 * At this point we can create a branch in the program based on the
			 * boundingConditions and array's reference expressions. Essentially
			 * we want to construct a runtime predicate that captures the
			 * assumptions about referenced memory locations that led to the
			 * judgement of independence.
			 * 
			 * For example if the program had for (int i=0; i<N; i++) a[i] =
			 * b[i]; then we want to generate a condition that says that: a != b
			 * && a+(N-1) < b && b+(N-1) < a which ensures that the array
			 * regions that are accessed are disjoint.
			 * 
			 * Note that this would approach could generalize to more
			 * interesting cases: for (int i=0; i<(N/2); i++) a[i] = a[N-1-i];
			 */

			/*
			 * Transform this "omp for" into a "omp single" workshare. To safely
			 * perform this when a reduction is present for an (op,var) pair all
			 * assignments to "var" in the "omp for" must be of the form
			 * "var = var op ...".
			 */
			SequenceNode<OmpReductionNode> reductionList = ompFor
					.reductionList();
			List<IdentifierNode> reductionVariables = null;
			boolean safeReduction = true;

			if (reductionList != null) {
				reductionVariables = new ArrayList<IdentifierNode>();

				// Build a map for scanning for reduction variable operator
				// assignment consistency
				Map<Entity, OmpReductionOperator> idOpMap = new HashMap<Entity, OmpReductionOperator>();
				for (OmpReductionNode r : reductionList) {
					if (r instanceof OmpSymbolReductionNode) {
						OmpReductionOperator op = ((OmpSymbolReductionNode) r)
								.operator();
						for (IdentifierExpressionNode id : r.variables()) {
							idOpMap.put(id.getIdentifier().getEntity(), op);
							reductionVariables.add(id.getIdentifier());
						}
						safeReduction &= checkReductionAssignments(fln,
								idOpMap);
					} else {
						safeReduction = false;
						break;
					}
				}
			}

			if (safeReduction) {
				ASTNode parent = ompFor.parent();
				int ompForIndex = getChildIndex(parent, ompFor);
				assert ompForIndex != -1;
				parent.removeChild(ompForIndex);

				fln.parent().removeChild(fln.childIndex());
				OmpWorksharingNode single = nodeFactory
						.newOmpSingleNode(ompFor.getSource(), fln);

				// Transfer private, firstprivate, copyprivate, and nowait
				// clauses to single

				SequenceNode<IdentifierExpressionNode> singlePrivateList = ompFor
						.privateList() != null
								? ompFor.privateList().copy()
								: null;
				SequenceNode<IdentifierExpressionNode> singleFirstPrivateList = ompFor
						.firstprivateList() != null
								? ompFor.firstprivateList().copy()
								: null;
				SequenceNode<IdentifierExpressionNode> singleCopyPrivateList = ompFor
						.copyprivateList() != null
								? ompFor.copyprivateList().copy()
								: null;

				// Add iteration variable to private list for single
				IdentifierExpressionNode privateLoopVariable = nodeFactory
						.newIdentifierExpressionNode(single.getSource(),
								nodeFactory.newIdentifierNode(
										single.getSource(),
										loopVariable.name()));
				if (ompFor.privateList() == null) {
					List<IdentifierExpressionNode> l = new ArrayList<IdentifierExpressionNode>();
					l.add(privateLoopVariable);
					singlePrivateList = nodeFactory
							.newSequenceNode(ompFor.getSource(), "private", l);
				} else {
					singlePrivateList.addSequenceChild(privateLoopVariable);
				}

				single.setPrivateList(singlePrivateList);
				single.setFirstprivateList(singleFirstPrivateList);

				// Any reduction variables should be added to copyprivate
				if (reductionVariables != null) {
					List<IdentifierExpressionNode> l = new ArrayList<IdentifierExpressionNode>();
					for (IdentifierNode id : reductionVariables) {
						l.add(nodeFactory
								.newIdentifierExpressionNode(single.getSource(),
										nodeFactory.newIdentifierNode(
												single.getSource(),
												id.name())));
					}
					if (ompFor.copyprivateList() == null) {
						singleCopyPrivateList = nodeFactory.newSequenceNode(
								ompFor.getSource(), "copyprivate", l);
					} else {
						for (IdentifierExpressionNode ide : l) {
							singleCopyPrivateList.addSequenceChild(ide);
						}
					}
				}

				single.setCopyprivateList(singleCopyPrivateList);
				single.setNowait(ompFor.nowait());

				parent.setChild(ompForIndex, single);
			}
		}

		allIndependent &= independent;

	}

	private boolean checkReductionAssignments(ASTNode node,
			Map<Entity, OmpReductionOperator> idOpMap) {
		return checkReductionWorker(node, idOpMap, true);
	}

	private boolean checkReductionWorker(ASTNode node,
			Map<Entity, OmpReductionOperator> idOpMap, boolean consistent) {
		if (node instanceof OperatorNode) {
			/*
			 * Access the LHS to prepare for operator comparison
			 */
			ExpressionNode lhs = ((OperatorNode) node).getArgument(0);
			if (lhs instanceof IdentifierExpressionNode) {
				Entity idEnt = ((IdentifierExpressionNode) lhs).getIdentifier()
						.getEntity();
				if (idOpMap.keySet().contains(idEnt)) {
					Operator op = OmpReduceOp2CivlOp(idOpMap.get(idEnt));

					switch (((OperatorNode) node).getOperator()) {
						case ASSIGN :
							ExpressionNode rhs = ((OperatorNode) node)
									.getArgument(1);
							if (rhs instanceof OperatorNode) {
								consistent &= (eqOpToOp(
										op) == ((OperatorNode) rhs)
												.getOperator());
							} else {
								consistent = false;
							}
							break;
						case BITANDEQ :
						case BITOREQ :
						case BITXOREQ :
						case MINUSEQ :
						case PLUSEQ :
						case TIMESEQ :
						case LAND :
						case LOR :
							consistent &= (((OperatorNode) node)
									.getOperator() == op);
							break;
						case EQUALS :
						case NEQ :
						default :
					}
				}
			}

		} else if (node != null) {
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				consistent &= checkReductionWorker(child, idOpMap, consistent);
			}
		}
		return consistent;
	}

	private Operator OmpReduceOp2CivlOp(
			OmpReductionOperator ompReductionOperator) {
		switch (ompReductionOperator) {
			case SUM :
				return Operator.PLUSEQ;
			case MINUS :
				return Operator.MINUSEQ;
			case PROD :
				return Operator.TIMESEQ;
			case BAND :
				return Operator.BITANDEQ;
			case BOR :
				return Operator.BITOREQ;
			case BXOR :
				return Operator.BITXOREQ;
			case LAND :
				return Operator.LAND;
			case LOR :
				return Operator.LOR;
			case EQV :
				return Operator.EQUALS;
			case NEQ :
				return Operator.NEQ;
			case MIN :
			case MAX :
			default :
				throw new CIVLUnimplementedFeatureException(
						"Unsupport OpenMP Reduce Operator: "
								+ ompReductionOperator);
		}
	}

	/*
	 * Returns the index of "child" in the children of "node"; -1 if "child" is
	 * not one of "node"'s children.
	 */
	private int getChildIndex(ASTNode node, ASTNode child) {
		for (int childIndex = 0; childIndex < node
				.numChildren(); childIndex++) {
			if (node.child(childIndex) == child)
				return childIndex;
		}
		return -1;
	}

	private Operator eqOpToOp(Operator op) {
		switch (op) {
			case BITANDEQ :
				return Operator.BITAND;
			case BITOREQ :
				return Operator.BITOR;
			case BITXOREQ :
				return Operator.BITXOR;
			case MINUSEQ :
				return Operator.MINUS;
			case PLUSEQ :
				return Operator.PLUS;
			case TIMESEQ :
				return Operator.TIMES;
			default :
		}
		return op;
	}

	private boolean isAssignment(ASTNode node) {
		return (node instanceof OperatorNode)
				&& (((OperatorNode) node).getOperator() == Operator.ASSIGN
						|| ((OperatorNode) node)
								.getOperator() == Operator.PLUSEQ
						|| ((OperatorNode) node)
								.getOperator() == Operator.POSTINCREMENT
						|| ((OperatorNode) node)
								.getOperator() == Operator.POSTDECREMENT);
	}

	/*
	 * This is a visitor that processes assignment statements.
	 * 
	 * It detects when it descends into a critical section and ignores writes to
	 * shared variables nested within.
	 */
	private void collectAssignRefExprs(ASTNode node) {
		if (node instanceof VariableDeclarationNode) {
			VariableDeclarationNode varDecl = (VariableDeclarationNode) node;
			Set<Entity> locallyDecls = locallyDeclaredEntities.peek();

			locallyDecls.add(varDecl.getEntity());
		} else if (node instanceof OmpSyncNode && ((OmpSyncNode) node)
				.ompSyncNodeKind() == OmpSyncNode.OmpSyncNodeKind.CRITICAL) {
			// Do not collect read/write references from critical sections
			return;
		} else if (isAssignment(node)) {
			/*
			 * Need to handle all of the *EQ operators as well.
			 */
			OperatorNode assign = (OperatorNode) node;
			ExpressionNode lhs = assign.getArgument(0);
			Set<Entity> locallyDecls = locallyDeclaredEntities.peek();

			// It's possible there are Post(Pre)Increment(Decrement) in
			// left-hand side expression (Modified and commented by Ziqing):
			collectAssignRefExprs(lhs);
			if (lhs instanceof IdentifierExpressionNode) {
				Entity idEnt = ((IdentifierExpressionNode) lhs).getIdentifier()
						.getEntity();

				if (!privateIDs.contains(idEnt)
						&& !loopPrivateIDs.contains(idEnt)
						&& !locallyDecls.contains(idEnt)) {
					writeVars.add(idEnt);
				}
			} else if (lhs instanceof OperatorNode && ((OperatorNode) lhs)
					.getOperator() == Operator.SUBSCRIPT) {
				Entity idEnt = baseArray((OperatorNode) lhs).getIdentifier()
						.getEntity();

				if (!privateIDs.contains(idEnt)
						&& !loopPrivateIDs.contains(idEnt)
						&& !locallyDecls.contains(idEnt)) {
					writeArrayRefs.add((OperatorNode) lhs);
				}

			} else {

			}

			// The argument at index 1 is the RHS. If there is no RHS then this
			// is a unary assignment and
			// we should collect from argument 0.
			ASTNode rhs = (assign.getNumberOfArguments() > 1)
					? assign.getArgument(1)
					: lhs;

			collectRHSRefExprs(rhs);

		} else if (node instanceof IfNode) {
			// Collect up the expressions from other statements
			IfNode ifn = (IfNode) node;
			collectRHSRefExprs(ifn.getCondition());
			collectAssignRefExprs(ifn.getTrueBranch());
			if (ifn.getTrueBranch() != null) {
				collectAssignRefExprs(ifn.getFalseBranch());
			}

		} else if (node instanceof LoopNode) {
			LoopNode loopn = (LoopNode) node;
			collectRHSRefExprs(loopn.getCondition());
			collectAssignRefExprs(loopn.getBody());

			if (loopn instanceof ForLoopNode) {
				ForLoopNode forn = (ForLoopNode) loopn;
				collectAssignRefExprs(forn.getInitializer());
				collectAssignRefExprs(forn.getIncrementer());
			}

		} else if (node instanceof SwitchNode) {
			SwitchNode switchn = (SwitchNode) node;
			collectRHSRefExprs(switchn.getCondition());
			collectAssignRefExprs(switchn.getBody());

		} else if (node instanceof ReturnNode) {
			ReturnNode returnn = (ReturnNode) node;
			if (returnn.getExpression() != null) {
				collectAssignRefExprs(returnn.getExpression());
			}

		} else if (node != null) {
			// BUG: can get here with null values in parallelfor.c example

			/*
			 * Could match other types here that have no ForLoopNode below them
			 * and skip their traversal to speed things up.
			 */
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				collectAssignRefExprs(child);
			}
		}
	}

	/*
	 * This is a visitor that processes assignment statements
	 */
	private void collectRHSRefExprs(ASTNode node) {
		if (node instanceof IdentifierExpressionNode) {
			Entity idEnt = ((IdentifierExpressionNode) node).getIdentifier()
					.getEntity();
			if (!privateIDs.contains(idEnt)
					&& !loopPrivateIDs.contains(idEnt)) {
				readVars.add(idEnt);
			}

		} else if (node instanceof OperatorNode
				&& ((OperatorNode) node).getOperator() == Operator.SUBSCRIPT) {
			Entity idEnt = baseArray((OperatorNode) node).getIdentifier()
					.getEntity();
			if (!privateIDs.contains(idEnt)
					&& !loopPrivateIDs.contains(idEnt)) {
				readArrayRefs.add((OperatorNode) node);
			}

		} else if (node != null) {
			// BUG: can get here with null values in parallelfor.c example

			/*
			 * Could match other types here that have no ForLoopNode below them
			 * and skip their traversal to speed things up.
			 */
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				collectRHSRefExprs(child);
			}
		}
	}

	/*
	 * Check array read/write sets for dependences
	 * 
	 * This code formulates a logical constraint for each pair of array refs on
	 * the LHS and RHS of the loop.
	 * 
	 * If there exists in the loop, statements of the form: a[e1] = ... and ...
	 * = ... a[e2] ... where e1 and e2 are distinct expressions written in terms
	 * of the loop index variable, then it must be the case that for all values
	 * of the index variable that satisfy initCondition and exitCondition that
	 * e1 == e2.
	 * 
	 * Note that if the index expressions are identical then there is no loop
	 * carried dependence. More generally if their equivalence is valid.
	 * 
	 * TBD: Currently this analysis does not handle copy statements and may
	 * therefore overestimate dependences
	 * 
	 * TBD: Currently this code assumes that one dimension is dependent on the
	 * for iteration variables. Needs to be extended for collapse.
	 */
	private boolean noArrayRefDependences(
			List<ExpressionNode> boundingConditions, Set<OperatorNode> writes,
			Set<OperatorNode> reads) {
		for (OperatorNode w : writes) {
			IdentifierExpressionNode baseWrite = baseArray(w);

			for (OperatorNode r : reads) {
				IdentifierExpressionNode baseRead = baseArray(r);

				if (baseWrite.getIdentifier().getEntity() == baseRead
						.getIdentifier().getEntity()) {

					if (debug) {
						System.out.println("Checking Array Refs for:");
						System.out.println("  " + baseWrite + "["
								+ indexExpression(w, 1) + "]");
						System.out.println("  " + baseRead + "["
								+ indexExpression(r, 1) + "]");
						System.out.println("with bounding conditions:"
								+ boundingConditions);
					}

					if (!noArrayRefDependencesWorker(boundingConditions, w, r))
						return false;
					// // if expressions are identical then there is no loop
					// // carried dependence
					// if (!identicalExprs(indexExpression(w, 1),
					// indexExpression(r, 1))) {
					// // Need to check logical equality of these expressions
					// if (!ExpressionEvaluator.checkEqualityWithConditions(
					// indexExpression(w, 1), indexExpression(r, 1),
					// boundingConditions)) {
					// return false;
					// }
					// }
				}
			}
		}
		return true;
	}

	/**
	 * <p>
	 * This is a worker method of {@link #noArrayRefDependences(List, Set, Set)}
	 * . For the LHS and RHS expression <code>a0[e0] = ... a1[e1] ...;</code>,
	 * this method will not only check e0 and e1 as described in
	 * {@link #noArrayRefDependences(List, Set, Set)} but also check if a0 and
	 * a1 are distinct and values of a0 and a1 will not change with loop
	 * iterations.
	 * </p>
	 * 
	 * <p>
	 * Currently it only recursively explores a fixed pattern for a0 and a1:
	 * Array[idx_0][...][idx_n]. Use idx_i_a, idx_i_b to represent the index
	 * expression in a0 and a1 respectively at the i-th dimension. If exists a j
	 * that 0 &lt= j &lt= n and idx_j_a and idx_j_b are distinct and both of
	 * them have no shared written entities, a0 and a1 are distinct.
	 * </p>
	 * 
	 * 
	 * @param boundingConditions
	 * @param w
	 * @param r
	 * @return
	 */
	private boolean noArrayRefDependencesWorker(
			List<ExpressionNode> boundingConditions, OperatorNode w,
			OperatorNode r) {
		ExpressionNode array_w = w.getArgument(0);
		ExpressionNode array_r = r.getArgument(0);

		if (array_w instanceof OperatorNode
				&& array_r instanceof OperatorNode) {
			OperatorNode casted_array_w = (OperatorNode) array_w;
			OperatorNode casted_array_r = (OperatorNode) array_r;

			if (casted_array_w.getOperator() == Operator.SUBSCRIPT
					&& casted_array_r.getOperator() == Operator.SUBSCRIPT)
				if (isSubArrayIndependent(casted_array_w, casted_array_r,
						boundingConditions))
					return true;
		}
		// if the two arrays are not in subscript form, consider they are
		// equivalent. see precondition of this method. Then compare the two
		// indices.

		// if expressions are identical then there is no loop
		// carried dependence
		if (!identicalExprs(indexExpression(w, 1), indexExpression(r, 1))) {
			// Need to check logical equality of these expressions
			if (!ExpressionEvaluator.checkEqualityWithConditions(
					indexExpression(w, 1), indexExpression(r, 1),
					boundingConditions)) {
				return false;
			}
		}
		return true;
	}

	/**
	 * <p>
	 * Returns true iff the given written-array and read-array: a[e0] and a[e1]
	 * are independent. i.e. For any two different threads t, t', the read-array
	 * of t, can never be the written array of t' at any time.
	 * </p>
	 * 
	 * <p>
	 * Note that the <strong>Assumption</strong> is the two arrays are both in
	 * the {@link Operator#SUBSCRIPT} form the super-arrays in the SUBCRIPT
	 * operations are identical. Hence the two given arrays are independent iff
	 * e0 and e1 are distinct and both of them contain no shared written entity.
	 * </p>
	 * 
	 * @param array_w
	 * @param array_r
	 * @return
	 */
	private boolean isSubArrayIndependent(OperatorNode array_w,
			OperatorNode array_r, List<ExpressionNode> boundingConditions) {
		ExpressionNode idx_w = indexExpression(array_w, 1);
		ExpressionNode idx_r = indexExpression(array_r, 1);
		ExpressionNode superArray_w = array_w.getArgument(0);
		ExpressionNode superArray_r = array_r.getArgument(0);

		if (superArray_w instanceof OperatorNode
				&& superArray_r instanceof OperatorNode) {
			OperatorNode castedSuperArray_w = (OperatorNode) superArray_w;
			OperatorNode castedSuperArray_r = (OperatorNode) superArray_r;

			if (castedSuperArray_w.getOperator() == Operator.SUBSCRIPT
					&& castedSuperArray_r.getOperator() == Operator.SUBSCRIPT)
				if (isSubArrayIndependent(array_w, array_r, boundingConditions))
					return true;
		}
		/*
		 * If cannot prove idx_w and idx_r are distinct (e.g. i and i + 1),
		 * return false; Otherwise keep checking if idx_w and idx_r have no
		 * shared written entities:
		 */
		if (!ExpressionEvaluator.checkInequalityWithConditions(idx_w, idx_r,
				boundingConditions))
			return false;

		/*
		 * If there is no shared written entities in idx_w and idx_r, the two
		 * given array are distinct. i.e. For any thread t, the array_w is never
		 * going to be the array_r of any other threads.
		 */
		ASTNode visitor = idx_w;
		ASTNode parent = idx_w.parent();
		int childIdx = idx_w.childIndex();
		int hasWrittenEntities = -1;

		visitor.remove();
		while (visitor != null) {
			if (visitor instanceof IdentifierNode) {
				Entity entity = ((IdentifierNode) visitor).getEntity();

				if (writeVars.contains(entity)
						&& !locallyDeclaredEntities.contains(entity)) {
					hasWrittenEntities++;
					break;
				}
			}
			visitor = visitor.nextDFS();
		}
		parent.setChild(childIdx, idx_w);

		visitor = idx_r;
		parent = idx_r.parent();
		childIdx = idx_r.childIndex();
		visitor.remove();
		while (visitor != null) {
			if (visitor instanceof IdentifierNode) {
				Entity entity = ((IdentifierNode) visitor).getEntity();

				if (writeVars.contains(entity)
						&& !locallyDeclaredEntities.contains(entity)) {
					hasWrittenEntities++;
					break;
				}
			}
			visitor = visitor.nextDFS();
		}
		parent.setChild(childIdx, idx_r);
		return hasWrittenEntities < 0;
	}

	private boolean identicalExprs(ExpressionNode x, ExpressionNode y) {
		boolean result = false;

		if (x instanceof IdentifierExpressionNode) {
			IdentifierExpressionNode xId = (IdentifierExpressionNode) x;
			if (y instanceof IdentifierExpressionNode) {
				IdentifierExpressionNode yId = (IdentifierExpressionNode) y;
				result = xId.getIdentifier().getEntity()
						.equals(yId.getIdentifier().getEntity());
			}
		} else if (x instanceof ConstantNode) {
			ConstantNode xConst = (ConstantNode) x;
			if (y instanceof ConstantNode) {
				ConstantNode yConst = (ConstantNode) y;
				result = xConst.getConstantValue()
						.equals(yConst.getConstantValue());
			}
		} else if (x instanceof OperatorNode) {
			OperatorNode xOp = (OperatorNode) x;

			if (y instanceof OperatorNode) {
				OperatorNode yOp = (OperatorNode) y;
				if (yOp.getOperator().equals(xOp.getOperator())) {
					if (yOp.getNumberOfArguments() == xOp
							.getNumberOfArguments()) {
						result = true; // initialize with "zero" for iterative
										// conjunction
						for (int i = 0; i < xOp.getNumberOfArguments(); i++) {
							result &= identicalExprs(xOp.getArgument(i),
									yOp.getArgument(i));
						}
					}
				}
			} else {
				assert false : "OpenMPSimplifier : cannot compare expression "
						+ x;
			}
		}
		return result;
	}

	/* This is a weaker version of the test that just compares base arrays */
	private boolean noArrayRefDependences(Set<OperatorNode> writes,
			Set<OperatorNode> reads) {
		for (OperatorNode w : writes) {
			IdentifierExpressionNode baseWrite = baseArray(w);

			for (OperatorNode r : reads) {
				IdentifierExpressionNode baseRead = baseArray(r);

				if (baseWrite.getIdentifier().getEntity() == baseRead
						.getIdentifier().getEntity()) {
					return false;
				}
			}
		}
		return true;
	}

	/*
	 * Determine whether node lexically contains an omp construct
	 */
	private boolean hasOmpConstruct(ASTNode node) {
		boolean result = false;
		if (node instanceof OmpNode) {
			result = true;
		} else if (node instanceof FunctionCallNode
				&& ((FunctionCallNode) node)
						.getFunction() instanceof IdentifierExpressionNode
				&& ((IdentifierExpressionNode) ((FunctionCallNode) node)
						.getFunction()).getIdentifier().name()
								.startsWith("omp_")) {
			result = true;
		} else if (node != null) {
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				result |= hasOmpConstruct(child);
				if (result)
					break;
			}
		}
		return result;
	}

	/*
	 * For a given subscript node recursively traverse down the 0th argument of
	 * the nested subscript expressions to return the base array identifier.
	 */
	private IdentifierExpressionNode baseArray(OperatorNode subscript) {
		assert subscript
				.getOperator() == OperatorNode.Operator.SUBSCRIPT : "Expected subscript expression";
		if (subscript.getArgument(0) instanceof IdentifierExpressionNode)
			return (IdentifierExpressionNode) subscript.getArgument(0);
		else if (subscript.getArgument(0) instanceof OperatorNode)
			return baseArray((OperatorNode) subscript.getArgument(0));
		// dxu: structure array
		else if (subscript.getArgument(0) instanceof CommonDotNode) {
			ASTNode arrayNode = subscript.getArgument(0).child(0);

			assert arrayNode instanceof OperatorNode;
			if (arrayNode instanceof OperatorNode)
				return baseArray((OperatorNode) arrayNode);
		} else
			assert false : "unknow type " + subscript.getArgument(0).getType();

		return null;
	}

	/*
	 * For multi-dimensional arrays the index expressions are nested in reverse
	 * order of source text nesting. The 1st index is the deepest, etc. Here we
	 * recurse down the 0th argument then count back up to return the
	 * appropriate index expression.
	 */
	private ExpressionNode indexExpression(OperatorNode subscript,
			int dimension) {
		assert subscript
				.getOperator() == OperatorNode.Operator.SUBSCRIPT : "Expected subscript expression";
		int d = indexExpressionDepth(subscript) - dimension;
		return indexExpressionAtDepth(subscript, d);
	}

	private ExpressionNode indexExpressionAtDepth(OperatorNode subscript,
			int depth) {
		assert subscript
				.getOperator() == OperatorNode.Operator.SUBSCRIPT : "Expected subscript expression";
		if (depth == 0) {
			return (ExpressionNode) subscript.getArgument(1);
		}
		return indexExpressionAtDepth(subscript, depth - 1);
	}

	private int indexExpressionDepth(OperatorNode subscript) {
		assert subscript
				.getOperator() == OperatorNode.Operator.SUBSCRIPT : "Expected subscript expression";
		if (subscript.getArgument(0) instanceof IdentifierExpressionNode) {
			return 1;
		}
		return indexExpressionDepth((OperatorNode) subscript.getArgument(0))
				+ 1;
	}

}
