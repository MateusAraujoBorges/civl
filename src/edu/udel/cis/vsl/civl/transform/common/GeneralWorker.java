package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity.EntityKind;
import edu.udel.cis.vsl.abc.ast.entity.IF.Function;
import edu.udel.cis.vsl.abc.ast.entity.IF.OrdinaryEntity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Variable;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.DeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ArrayLambdaNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CastNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode.TypeNodeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.type.IF.Type.TypeKind;
import edu.udel.cis.vsl.abc.front.IF.CivlcTokenConstant;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.transform.IF.NameTransformer;
import edu.udel.cis.vsl.abc.transform.IF.Transform;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.transform.IF.GeneralTransformer;

/**
 * The general transformer performs the following transformations:
 * 
 * <ul>
 * <li>malloc(...) to $malloc($gen_root, ...); where $gen_root is the root scope
 * of this AST (which is reserved as a relative root if other transformers make
 * this AST as part of another)</li>
 * <li>
 * introduce input variables for argc and argv</li>
 * <li>
 * introduce new file scope function $gen_root_function that calls the main
 * function</li>
 * <li>arguments of the main function argc and argv become input variables</li>
 * <li>static variables are all moved to the root scope</li>
 * </ul>
 * 
 * @author Manchun Zheng
 *
 */
public class GeneralWorker extends BaseWorker {

	private final static String MALLOC = "malloc";
	final static String GENERAL_ROOT = ModelConfiguration.GENERAL_ROOT;
	private final static String separator = "$";
	private int static_var_count = 0;
	private String CIVL_argc_name;
	private String CIVL_argv_name;
	private Source mainSource;
	/**
	 * static variable declaration nodes of this AST
	 */
	private List<VariableDeclarationNode> static_variables = new LinkedList<>();
	private boolean argcUsed = false;
	private boolean argvUsed = false;

	public GeneralWorker(ASTFactory astFactory) {
		super(GeneralTransformer.LONG_NAME, astFactory);
		this.identifierPrefix = GeneralTransformer.PREFIX;
	}

	@Override
	public AST transform(AST unit) throws SyntaxException {
		SequenceNode<BlockItemNode> root = unit.getRootNode();
		AST newAst;
		List<VariableDeclarationNode> inputVars = new ArrayList<>();
		List<BlockItemNode> newExternalList = new ArrayList<>();
		OrdinaryEntity mainEntity = unit.getInternalOrExternalEntity(MAIN);
		FunctionDefinitionNode newMainFunction = null;
		Function mainFunction;
		FunctionDefinitionNode mainDef;

		if (mainEntity == null) {
			throw new SyntaxException("missing main function", unit
					.getRootNode().getSource());
		}
		if (!(mainEntity instanceof Function)) {
			throw new SyntaxException("non-function entity with name \"main\"",
					mainEntity.getFirstDeclaration().getSource());
		}
		mainFunction = (Function) mainEntity;
		mainDef = mainFunction.getDefinition();
		checkAgumentsOfMainFunction(mainDef, root);
		unit = renameStaticVariables(unit);
		unit.release();
		root = moveStaticVariables(root);
		processMalloc(root);
		// remove main prototypes...
		for (DeclarationNode decl : mainFunction.getDeclarations()) {
			if (!decl.isDefinition()) {
				decl.parent().removeChild(decl.childIndex());
			}
		}
		this.mainSource = mainDef.getSource();
		inputVars = getInputVariables(mainDef);
		if (inputVars.size() > 0) {
			// the original main has parameters, need to transform main to _main
			// TODO add new argv _argv
			transformMainFunction(root);
			newMainFunction = createNewMainFunction();
		}
		// no need to modify the body of main
		for (BlockItemNode inputVar : inputVars)
			newExternalList.add(inputVar);
		// add my root
		newExternalList.add(this.generalRootScopeNode());
		for (BlockItemNode child : root) {
			if (child != null) {
				newExternalList.add(child);
				child.parent().removeChild(child.childIndex());
			}
		}
		if (newMainFunction != null)
			newExternalList.add(newMainFunction);
		root = nodeFactory.newSequenceNode(root.getSource(), "TranslationUnit",
				newExternalList);
		this.completeSources(root);
		newAst = astFactory.newAST(root, unit.getSourceFiles(),
				unit.isWholeProgram());
		// newAst.prettyPrint(System.out, false);
		return newAst;
	}

	private void checkAgumentsOfMainFunction(FunctionDefinitionNode main,
			SequenceNode<BlockItemNode> root) {
		FunctionTypeNode functionType = main.getTypeNode();
		SequenceNode<VariableDeclarationNode> parameters = functionType
				.getParameters();

		if (parameters.numChildren() == 2)
			this.checkAgumentsOfMainFunctionWorker(
					parameters.getSequenceChild(0),
					parameters.getSequenceChild(1), main.getBody());
	}

	private void checkAgumentsOfMainFunctionWorker(
			VariableDeclarationNode argc, VariableDeclarationNode argv,
			ASTNode node) {
		if (node instanceof IdentifierExpressionNode) {
			IdentifierNode identifier = ((IdentifierExpressionNode) node)
					.getIdentifier();
			Entity entity = identifier.getEntity();

			if (entity.getEntityKind() == EntityKind.VARIABLE) {
				VariableDeclarationNode variable = ((Variable) entity)
						.getDefinition();

				if (variable != null)
					if (variable.equals(argc))
						this.argcUsed = true;
					else if (variable.equals(argv))
						this.argvUsed = true;
			}
		} else {
			for (ASTNode child : node.children()) {
				if (child == null)
					continue;
				checkAgumentsOfMainFunctionWorker(argc, argv, child);
				if (this.argcUsed && this.argvUsed)
					return;
			}
		}
	}

	private ExpressionNode argv_value_node() throws SyntaxException {
		TypeNode arrayOfCharPointer = nodeFactory.newArrayTypeNode(this
				.newSource("new main function", CivlcTokenConstant.TYPE),
				nodeFactory.newPointerTypeNode(this.newSource(
						"new main function", CivlcTokenConstant.POINTER), this
						.basicType(BasicTypeKind.CHAR)), this
						.identifierExpression(CIVL_argc_name));
		// ExpressionNode body =
		// this.nodeFactory.newOperatorNode(this.newSource(
		// "address of", CivlcTokenConstant.SUB), Operator.ADDRESSOF,
		// this.nodeFactory.newOperatorNode(this.newSource("subscript",
		// CivlcTokenConstant.SUB), Operator.SUBSCRIPT,
		// this.nodeFactory.newOperatorNode(this.newSource(
		// "subscript", CivlcTokenConstant.SUB),
		// Operator.SUBSCRIPT, this
		// .identifierExpression(CIVL_argv_name),
		// this.identifierExpression("i")), this
		// .integerConstant(0)));

		ExpressionNode body = this.nodeFactory.newOperatorNode(
				this.newSource("subscript", CivlcTokenConstant.SUB),
				Operator.SUBSCRIPT, this.identifierExpression(CIVL_argv_name),
				this.identifierExpression("i"));

		ArrayLambdaNode arrayLambda = this.nodeFactory.newArrayLambdaNode(
				this.newSource("array lambda", CivlcTokenConstant.LAMBDA),
				arrayOfCharPointer,
				Arrays.asList(this.variableDeclaration("i",
						this.basicType(BasicTypeKind.INT))), null, body);

		// ExpressionNode addressOf_argv0 = nodeFactory.newOperatorNode(this
		// .newSource("new main function", CivlcTokenConstant.OPERATOR),
		// Operator.SUBSCRIPT, Arrays.asList(arrayLambda, nodeFactory
		// .newIntegerConstantNode(this.newSource(
		// "new main function",
		// CivlcTokenConstant.INTEGER_CONSTANT), "0")));
		// addressOf_argv0 = nodeFactory.newOperatorNode(this.newSource(
		// "new main function", CivlcTokenConstant.OPERATOR),
		// Operator.ADDRESSOF, Arrays.asList(addressOf_argv0));

		return arrayLambda;
	}

	// private VariableDeclarationNode create_argv_tmp() throws SyntaxException
	// {
	// TypeNode arrayOfCharPointer = nodeFactory.newArrayTypeNode(this
	// .newSource("new main function", CivlcTokenConstant.TYPE),
	// nodeFactory.newPointerTypeNode(this.newSource(
	// "new main function", CivlcTokenConstant.POINTER), this
	// .basicType(BasicTypeKind.CHAR)), this
	// .identifierExpression(CIVL_argc_name));
	//
	// return this
	// .variableDeclaration(
	// _argv_tmp_name,
	// arrayOfCharPointer,
	// this.nodeFactory.newArrayLambdaNode(
	// this.newSource("array lambda",
	// CivlcTokenConstant.LAMBDA),
	// arrayOfCharPointer.copy(),
	// this.nodeFactory.newSequenceNode(
	// this.newSource(
	// "bound variable of array lambda",
	// CivlcTokenConstant.DECLARATION_LIST),
	// "bound variable list",
	// Arrays.asList(this.nodeFactory.newPairNode(
	// this.newSource("pair", 0),
	// this.nodeFactory.newSequenceNode(
	// this.newSource(
	// "variable declaration",
	// 0),
	// "variables",
	// Arrays.asList(this
	// .variableDeclaration(
	// "i",
	// this.basicType(BasicTypeKind.INT)))),
	// null))),
	// null,
	// this.nodeFactory.newOperatorNode(
	// this.newSource("address of",
	// CivlcTokenConstant.SUB),
	// Operator.ADDRESSOF,
	// this.nodeFactory.newOperatorNode(
	// this.newSource("subscript",
	// CivlcTokenConstant.SUB),
	// Operator.SUBSCRIPT,
	// this.nodeFactory.newOperatorNode(
	// this.newSource(
	// "subscript",
	// CivlcTokenConstant.SUB),
	// Operator.SUBSCRIPT,
	// this.identifierExpression(CIVL_argv_name),
	// this.identifierExpression("i")),
	// this.integerConstant(0)))));
	// }

	/**
	 * creates a new main function:
	 * 
	 * <pre>
	 * void main(){
	 *     for(int i=0; i &lt; 10; i = i + 1)
	 *       _argv[i] = &CIVL_argv[i][0];
	 *     _main(CIVL_argc, &_argv[0]);
	 * }
	 * </pre>
	 * 
	 * @return
	 * @throws SyntaxException
	 */
	private FunctionDefinitionNode createNewMainFunction()
			throws SyntaxException {
		FunctionCallNode callMain;
		List<BlockItemNode> blockItems = new LinkedList<>();
		FunctionTypeNode mainFuncType;

		callMain = nodeFactory.newFunctionCallNode(this.newSource(
				"new main function", CivlcTokenConstant.CALL), this
				.identifierExpression(GEN_MAIN), Arrays.asList(
				this.identifierExpression(CIVL_argc_name), argv_value_node()),
				null);
		blockItems.add(nodeFactory.newExpressionStatementNode(callMain));
		mainFuncType = nodeFactory.newFunctionTypeNode(mainSource, nodeFactory
				.newBasicTypeNode(mainSource, BasicTypeKind.INT), nodeFactory
				.newSequenceNode(this.newSource("new main function",
						CivlcTokenConstant.PARAMETER_TYPE_LIST),
						"formal parameter types",
						new LinkedList<VariableDeclarationNode>()), false);

		return nodeFactory.newFunctionDefinitionNode(this.mainSource,
				this.identifier(MAIN), mainFuncType, null,
				nodeFactory.newCompoundStatementNode(mainSource, blockItems));
	}

	private VariableDeclarationNode generalRootScopeNode() {
		return nodeFactory.newVariableDeclarationNode(mainSource,
				nodeFactory.newIdentifierNode(mainSource, GENERAL_ROOT),
				nodeFactory.newScopeTypeNode(mainSource),
				nodeFactory.newHereNode(mainSource));
	}

	private void processMalloc(ASTNode node) {
		if (node instanceof FunctionCallNode) {
			FunctionCallNode funcCall = (FunctionCallNode) node;

			if (funcCall.getFunction().expressionKind() == ExpressionKind.IDENTIFIER_EXPRESSION) {
				IdentifierExpressionNode functionExpression = (IdentifierExpressionNode) funcCall
						.getFunction();
				String functionName = functionExpression.getIdentifier().name();

				if (functionName.equals(MALLOC)) {
					ASTNode parent = funcCall.parent();
					ExpressionNode myRootScope = this.identifierExpression(
							funcCall.getSource(), GENERAL_ROOT);
					int callIndex = funcCall.childIndex();
					ExpressionNode argument = funcCall.getArgument(0);

					functionExpression.getIdentifier().setName("$" + MALLOC);
					argument.parent().removeChild(argument.childIndex());
					funcCall.setArguments(nodeFactory.newSequenceNode(
							argument.getSource(), "Actual Parameters",
							Arrays.asList(myRootScope, argument)));
					if (!(parent instanceof CastNode)) {
						funcCall.remove();
						if (parent instanceof OperatorNode) {
							ExpressionNode lhs = ((OperatorNode) parent)
									.getArgument(0);
							Type type = lhs.getInitialType();
							TypeNode typeNode;
							CastNode castNode;

							if (type.kind() != TypeKind.POINTER)
								throw new CIVLSyntaxException(
										"The left hand side of a malloc call must be of pointer"
												+ " type.", lhs.getSource());
							typeNode = this.typeNode(lhs.getSource(), type);
							castNode = nodeFactory.newCastNode(
									funcCall.getSource(), typeNode, funcCall);
							parent.setChild(callIndex, castNode);
						} else if (parent instanceof VariableDeclarationNode) {
							VariableDeclarationNode variable = (VariableDeclarationNode) parent;
							CastNode castNode = nodeFactory.newCastNode(
									funcCall.getSource(), variable
											.getTypeNode().copy(), funcCall);

							variable.setInitializer(castNode);
						}
					}
				}
			}
		} else {
			for (ASTNode child : node.children()) {
				if (child != null)
					processMalloc(child);
			}
		}

	}

	/**
	 * Processes the original main function, including:
	 * <ul>
	 * <li>Removes all arguments of the function;</li>
	 * </ul>
	 * 
	 * @param mainFunction
	 *            The function definition node representing the original main
	 *            function.
	 * @param vars
	 *            The list of variable declaration nodes that are the arguments
	 *            of the original main function. These variables will be moved
	 *            up to the higher scope (i.e., the file scope of the final AST)
	 *            and become $input variables of the final AST. When invoking
	 *            this function, this parameter should be an empty list and this
	 *            function will update this list.
	 * @throws SyntaxException
	 */
	private List<VariableDeclarationNode> getInputVariables(
			FunctionDefinitionNode mainFunction) throws SyntaxException {
		List<VariableDeclarationNode> inputVars = new ArrayList<>();
		FunctionTypeNode functionType = mainFunction.getTypeNode();
		SequenceNode<VariableDeclarationNode> parameters = functionType
				.getParameters();
		int count = parameters.numChildren();

		if (count != 0 && count != 2) {
			if (count == 1) {
				if (parameters.getSequenceChild(0).getTypeNode().typeNodeKind() != TypeNodeKind.VOID)
					throw new SyntaxException(
							"The main function should have 0 or 2 parameters instead of "
									+ count, mainFunction.getSource());
			} else
				throw new SyntaxException(
						"The main function should have 0 or 2 parameters instead of "
								+ count, mainFunction.getSource());
		}
		if (count == 2 && (this.argvUsed || this.argcUsed)) {
			VariableDeclarationNode argc = parameters.getSequenceChild(0);
			VariableDeclarationNode argv = parameters.getSequenceChild(1);
			VariableDeclarationNode CIVL_argc = argc.copy();
			VariableDeclarationNode CIVL_argv;
			String argcName = argc.getIdentifier().name();
			String argvName = argv.getIdentifier().name();

			this.CIVL_argc_name = identifierPrefix + argcName;
			this.CIVL_argv_name = identifierPrefix + argvName;
			CIVL_argc.getTypeNode().setInputQualified(true);
			CIVL_argc.getIdentifier().setName(this.CIVL_argc_name);
			inputVars.add(CIVL_argc);
			CIVL_argv = inputArgvDeclaration(argv, CIVL_argv_name);
			inputVars.add(CIVL_argv);
		} else if (count == 2) {
			functionType.setParameters(this.nodeFactory.newSequenceNode(
					parameters.getSource(), "Formal Parameter List",
					new ArrayList<VariableDeclarationNode>(0)));
		}
		return inputVars;
	}

	/**
	 * Declares <code>$input char CIVL_argv[MAX_ARGC][];</code>.
	 * 
	 * @param oldArgv
	 * @return
	 * @throws SyntaxException
	 */
	private VariableDeclarationNode inputArgvDeclaration(
			VariableDeclarationNode oldArgv, String argvNewName)
			throws SyntaxException {
		VariableDeclarationNode __argv = oldArgv.copy();
		Source source = oldArgv.getSource();
		TypeNode arrayOfString = nodeFactory.newArrayTypeNode(
				source,
				nodeFactory.newArrayTypeNode(oldArgv.getSource(),
						this.basicType(BasicTypeKind.CHAR), null),
				this.identifierExpression(CIVL_argc_name));

		__argv.getIdentifier().setName(argvNewName);
		arrayOfString.setInputQualified(true);
		__argv.setTypeNode(arrayOfString);
		return __argv;
	}

	public enum ArgvTypeKind {
		POINTER_POINTER_CHAR, ARRAY_POINTER_CHAR, ARRAY_ARRAY_CAHR
	};

	private AST renameStaticVariables(AST ast) throws SyntaxException {
		Map<Entity, String> newNameMap = new HashMap<>();
		NameTransformer staticVariableNameTransformer;

		newNameMap = newNameMapOfStaticVariables(ast.getRootNode(),
				ast.getRootNode(), newNameMap);
		staticVariableNameTransformer = Transform.nameTransformer(newNameMap,
				astFactory);
		return staticVariableNameTransformer.transform(ast);
	}

	// TODO can you have static for function parameters?
	// TODO what if the initializer of the variable node access some variables
	// not declared in the root scope?
	// TODO what if the type is defined somewhere in the AST?
	/**
	 * Computes the new name map of static variables. A static variable "var" is
	 * renamed to "var$n", where n is the current static variable ID.
	 * 
	 * @param node
	 * @param newNames
	 * @return
	 */
	private Map<Entity, String> newNameMapOfStaticVariables(ASTNode root,
			ASTNode node, Map<Entity, String> newNames) {
		if (node instanceof VariableDeclarationNode) {
			VariableDeclarationNode variable = (VariableDeclarationNode) node;

			if (variable.hasStaticStorage()) {
				String oldName = variable.getName();
				String newName = oldName + separator + this.static_var_count++;

				newNames.put(variable.getEntity(), newName);
				// don't move the variable if it is already in the root scope
				if (!variable.parent().equals(root))
					this.static_variables.add(variable);
			}
		} else {
			for (ASTNode child : node.children()) {
				if (child == null)
					continue;
				newNames = newNameMapOfStaticVariables(root, child, newNames);
			}
		}
		return newNames;
	}

	private SequenceNode<BlockItemNode> moveStaticVariables(
			SequenceNode<BlockItemNode> root) {
		if (this.static_variables.size() < 1)
			return root;

		List<BlockItemNode> newChildren = new LinkedList<>();
		int count = root.numChildren();

		for (VariableDeclarationNode var : this.static_variables) {
			var.remove();
			newChildren.add(var);
		}
		for (int i = 0; i < count; i++) {
			BlockItemNode child = root.getSequenceChild(i);

			if (child == null)
				continue;
			child.remove();
			newChildren.add(child);
		}
		return nodeFactory
				.newTranslationUnitNode(root.getSource(), newChildren);
	}
}
