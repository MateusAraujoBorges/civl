package edu.udel.cis.vsl.civl.transform.common;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.entity.IF.Variable;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.InitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.TypedefDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IntegerConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.ArrayTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.PointerTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.StructureOrUnionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.value.IF.IntegerValue;
import edu.udel.cis.vsl.abc.ast.value.IF.Value;
import edu.udel.cis.vsl.abc.front.IF.CivlcTokenConstant;
import edu.udel.cis.vsl.abc.front.c.preproc.CPreprocessor;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.transform.IF.SvcompUnPPTransformer;

/**
 * For *.i files, pruner will be applied first, and then svcomp transformer, and
 * link with implementation source, and then apply other language/standard
 * transformers as usual.
 * 
 * This class is responsible for the svcomp transformation
 * 
 * @author Manchun Zheng
 *
 */
public class SvcompUnPPWorker extends BaseWorker {

	private final static String PTHREAD_PREFIX = "pthread_";

	private final static String PTHREAD_HEADER = "pthread.h";

	private final static String IO_PREFIX = "_IO_";

	private final static String IO_HEADER = "stdio.h";

	private final static String EXIT = "exit";

	private final static String STRCPY = "strcpy";

	private final static String ABORT = "abort";

	private final static String PRINTF = "printf";

	private final static String STDLIB_HEADER = "stdlib.h";

	private final static String STRING_HEADER = "string.h";

	private boolean needsPthreadHeader = false;

	private boolean needsIoHeader = false;

	private boolean needsStdlibHeader = false;

	private boolean needsStringHeader = false;

	private final static int UPPER_BOUND = 11;// has to use this because of
												// pthread/fib_bench_longest_false-unreach-call.i

	private final static String SCALE_VAR = "scale";

	private Map<String, Integer> variableNamesIntializedBig = new HashMap<>();

	private Map<String, VariableDeclarationNode> variablesIntializedBig = new HashMap<>();

	private Map<Integer, VariableDeclarationNode> scalerVariableMap = new HashMap<>();

	public SvcompUnPPWorker(ASTFactory astFactory) {
		super(SvcompUnPPTransformer.LONG_NAME, astFactory);
		this.identifierPrefix = "_" + SvcompUnPPTransformer.CODE;
	}

	@Override
	public AST transform(AST ast) throws SyntaxException {
		SequenceNode<BlockItemNode> rootNode = ast.getRootNode();

		ast.release();
		// this.removeIoNodes(rootNode);
		// this.removePthreadTypedefs(rootNode);
		this.removeNodes(rootNode);
		rootNode = downScaler(rootNode);
		// rootNode.prettyPrint(System.out);
		this.completeSources(rootNode);
		ast = astFactory.newAST(rootNode, ast.getSourceFiles(),
				ast.isWholeProgram());
		ast = this.addHeaders(ast);
		// ast.prettyPrint(System.out, false);
		return ast;
	}

	private SequenceNode<BlockItemNode> downScaler(
			SequenceNode<BlockItemNode> root) throws SyntaxException {
		if (scalerVariableMap.size() > 0) {
			List<BlockItemNode> newItems = new ArrayList<>();
			VariableDeclarationNode scale_bound = this.variableDeclaration(
					this.identifierPrefix + "_" + SCALE_VAR,
					this.basicType(BasicTypeKind.INT));

			scale_bound.getTypeNode().setInputQualified(true);
			newItems.add(this.assumeFunctionDeclaration(
					this.newSource("$assume", CivlcTokenConstant.DECLARATION)));
			newItems.add(scale_bound);
			for (VariableDeclarationNode varNode : scalerVariableMap.values()) {
				varNode.setInitializer(
						this.identifierExpression(scale_bound.getName()));
				newItems.add(varNode);
				// newItems.add(this.assumeNode(this.nodeFactory.newOperatorNode(
				// varNode.getSource(), Operator.EQUALS,
				// this.identifierExpression(varNode.getName()),
				// this.identifierExpression(scale_bound.getName()))));
			}
			for (BlockItemNode item : root) {
				if (item == null)
					continue;

				downScalerWork(item);
				item.remove();
				newItems.add(item);
			}
			return this.nodeFactory.newSequenceNode(root.getSource(),
					"Translation Unit", newItems);
		}
		return root;
	}

	private void downScalerWork(ASTNode node) throws SyntaxException {
		if (node instanceof VariableDeclarationNode) {
			VariableDeclarationNode varDecl = (VariableDeclarationNode) node;
			TypeNode type = varDecl.getTypeNode();

			if (type instanceof ArrayTypeNode) {
				ArrayTypeNode arrayType = (ArrayTypeNode) type;
				ExpressionNode extent = arrayType.getExtent();

				if (extent instanceof IntegerConstantNode) {
					ExpressionNode newExtent = this.getDownScaledExpression(
							extent.getSource(),
							this.getIntValue((IntegerConstantNode) extent));

					if (newExtent != null)
						arrayType.setExtent(newExtent);
				}
			}
		} else if (node instanceof OperatorNode) {
			OperatorNode operatorNode = (OperatorNode) node;
			Operator operator = operatorNode.getOperator();
			boolean transformed = false;

			if (operator == Operator.DIV || operator == Operator.MINUS
					|| operator == Operator.PLUS || operator == Operator.TIMES
					|| operator == Operator.MOD) {
				try {

					Value value = this.nodeFactory
							.getConstantValue(operatorNode);

					if (value != null && (value instanceof IntegerValue)) {
						ExpressionNode newExpression = this
								.getDownScaledExpression(
										operatorNode.getSource(),
										((IntegerValue) value).getIntegerValue()
												.intValue());

						if (newExpression != null) {
							transformed = true;
							operatorNode.parent().setChild(
									operatorNode.childIndex(), newExpression);
						}
					}
				} catch (SyntaxException ex) {
					transformed = false;
				}
			}
			if (!transformed) {
				int numArgs = operatorNode.getNumberOfArguments();

				for (int i = 0; i < numArgs; i++) {
					ExpressionNode arg = operatorNode.getArgument(i);

					if (arg instanceof IntegerConstantNode) {
						ExpressionNode newArg = this.getDownScaledExpression(
								arg.getSource(),
								this.getIntValue((IntegerConstantNode) arg));

						if (newArg != null)
							operatorNode.setArgument(i, newArg);
					} else if (arg instanceof OperatorNode) {
						downScalerWork(arg);
					}
				}
			}
			// Operator operator = operatorNode.getOperator();
			// ExpressionNode upper = null;
			// int argIndex = -1;
			//
			// if (operator == Operator.LT || operator == Operator.LTE) {
			// upper = operatorNode.getArgument(1);
			// argIndex = 1;
			// } else if (operator == Operator.GT || operator == Operator.GTE) {
			// upper = operatorNode.getArgument(0);
			// argIndex = 0;
			// }
			// if (upper != null) {
			// if (upper instanceof IntegerConstantNode) {
			// ExpressionNode newArgument = this
			// .getDownScaledExpression((IntegerConstantNode) upper);
			//
			// if (newArgument != null)
			// operatorNode.setArgument(argIndex, newArgument);
			// }
			// }
		} else {
			for (ASTNode child : node.children()) {
				if (child == null)
					continue;
				downScalerWork(child);
			}
		}
	}

	private ExpressionNode getDownScaledExpression(Source source,
			int upperValue) throws SyntaxException {
		// int upperValue = ((IntegerConstantNode) constant).getConstantValue()
		// .getIntegerValue().intValue();
		if (scalerVariableMap.containsKey(upperValue)) {
			return this.identifierExpression(
					scalerVariableMap.get(upperValue).getName());
		} else if (scalerVariableMap.containsKey(upperValue - 1)) {
			ExpressionNode variableIdentifier = this.identifierExpression(
					scalerVariableMap.get(upperValue - 1).getName());

			return this.nodeFactory.newOperatorNode(source, Operator.PLUS,
					variableIdentifier, this.integerConstant(1));
		} else if (scalerVariableMap.containsKey(upperValue + 1)) {
			ExpressionNode variableIdentifier = this.identifierExpression(
					scalerVariableMap.get(upperValue + 1).getName());

			this.nodeFactory.newOperatorNode(source, Operator.MINUS,
					variableIdentifier, this.integerConstant(1));
		}
		return null;
	}

	private AST addHeaders(AST ast) throws SyntaxException {
		if (needsStdlibHeader) {
			AST stdlibHeaderAST = this.parseSystemLibrary(
					new File(CPreprocessor.ABC_INCLUDE_PATH, STDLIB_HEADER),
					EMPTY_MACRO_MAP);

			ast = this.combineASTs(stdlibHeaderAST, ast);
		}
		if (this.needsStringHeader) {
			AST stringlibHeaderAST = this.parseSystemLibrary(
					new File(CPreprocessor.ABC_INCLUDE_PATH, STRING_HEADER),
					EMPTY_MACRO_MAP);

			ast = this.combineASTs(stringlibHeaderAST, ast);
		}
		if (needsIoHeader) {
			AST ioHeaderAST = this.parseSystemLibrary(
					new File(CPreprocessor.ABC_INCLUDE_PATH, IO_HEADER),
					EMPTY_MACRO_MAP);

			ast = this.combineASTs(ioHeaderAST, ast);
		}
		if (needsPthreadHeader) {
			AST pthreadHeaderAST = this.parseSystemLibrary(
					new File(CPreprocessor.ABC_INCLUDE_PATH, PTHREAD_HEADER),
					EMPTY_MACRO_MAP);

			ast = this.combineASTs(pthreadHeaderAST, ast);
		}
		return ast;
	}

	private void removeNodes(SequenceNode<BlockItemNode> root)
			throws SyntaxException {
		for (BlockItemNode item : root) {
			boolean toRemove = false;

			if (item == null)
				continue;
			toRemove = isQualifiedIoNode(item);
			if (!toRemove)
				toRemove = isQualifiedPthreadNode(item);
			if (!toRemove) {
				toRemove = isStdlibNode(item);
			}
			if (!toRemove) {
				toRemove = isStringNode(item);
			}
			if (toRemove)
				item.remove();
			else if (item instanceof VariableDeclarationNode) {
				VariableDeclarationNode varDecl = (VariableDeclarationNode) item;
				TypeNode type = varDecl.getTypeNode();
				InitializerNode initializer = varDecl.getInitializer();

				if (type instanceof ArrayTypeNode) {
					ArrayTypeNode arrayType = (ArrayTypeNode) type;
					ExpressionNode extent = arrayType.getExtent();
					ExpressionNode newExtent = null;
					int intValue = -1;

					if (extent instanceof IntegerConstantNode) {
						// TODO for now make the input variables the same
						// storage class as the array
						intValue = this
								.getIntValue((IntegerConstantNode) extent);
					} else if (extent instanceof OperatorNode) {
						// search for things like 320*4+1
						Value value = this.nodeFactory.getConstantValue(extent);

						if (value != null && (value instanceof IntegerValue)) {
							intValue = ((IntegerValue) value).getIntegerValue()
									.intValue();
						}
					}
					newExtent = this.factorNewInputVariable(intValue,
							varDecl.hasStaticStorage());
					if (newExtent != null)
						arrayType.setExtent(newExtent);
				} else if (initializer != null) {
					if (initializer instanceof IntegerConstantNode) {
						int initValue = ((IntegerConstantNode) initializer)
								.getConstantValue().getIntegerValue()
								.intValue();
						String name = varDecl.getName();

						if (initValue > UPPER_BOUND) {
							this.variableNamesIntializedBig.put(name,
									initValue);
							this.variablesIntializedBig.put(name, varDecl);
						}
					}
				}
			} else if (item instanceof FunctionDefinitionNode) {
				this.checkBigLoopBound(
						((FunctionDefinitionNode) item).getBody());
			}
		}
	}

	private ExpressionNode factorNewInputVariable(int intValue,
			boolean isStatic) {
		// int intValue =
		// intConst.getConstantValue().getIntegerValue().intValue();
		if (intValue > UPPER_BOUND) {
			if (this.scalerVariableMap.containsKey(intValue)
					|| scalerVariableMap.containsKey(intValue - 1)
					|| scalerVariableMap.containsKey(intValue + 1))
				return null;

			VariableDeclarationNode scaleVariable = this.variableDeclaration(
					this.newUniqueIdentifier(SCALE_VAR),
					this.basicType(BasicTypeKind.INT));

			// scaleVariable.getTypeNode().setInputQualified(true);
			scaleVariable.setStaticStorage(isStatic);
			this.scalerVariableMap.put(intValue, scaleVariable);
			return this.identifierExpression(scaleVariable.getName());
		}
		return null;
	}

	private void checkBigLoopBound(ASTNode node) throws SyntaxException {
		// look for
		// while(i<1000){...; i=i+1;} or
		// do{...; i=i+1;}while(i<1000) or
		// for(;i<1000;i++)
		if (node instanceof LoopNode) {
			ExpressionNode condition = ((LoopNode) node).getCondition();

			if (condition instanceof OperatorNode) {
				OperatorNode operatorNode = (OperatorNode) condition;
				Operator operator = operatorNode.getOperator();
				ExpressionNode upper = null;
				int argIndex = -1;

				if (operator == Operator.LT || operator == Operator.LTE) {
					upper = operatorNode.getArgument(1);
					argIndex = 1;
				} else if (operator == Operator.GT
						|| operator == Operator.GTE) {
					upper = operatorNode.getArgument(0);
					argIndex = 0;
				}
				if (upper != null) {
					ExpressionNode newUpper = transformBigValueNode(upper);

					if (newUpper != null)
						operatorNode.setArgument(argIndex, newUpper);
				}
				IdentifierExpressionNode array = findArrayReference(
						operatorNode);

				if (array != null) {
					Variable arrayVariable = (Variable) array.getIdentifier()
							.getEntity();
					VariableDeclarationNode arrayDef = arrayVariable
							.getDefinition();
					ArrayTypeNode arrayType = (ArrayTypeNode) arrayDef
							.getTypeNode();
					ExpressionNode extent = arrayType.getExtent();

					if (extent instanceof IntegerConstantNode) {
						this.factorNewInputVariable(
								this.getIntValue((IntegerConstantNode) extent),
								false);
					}
				}
			}
		} else {
			for (ASTNode child : node.children()) {
				if (child != null)
					this.checkBigLoopBound(child);
			}
		}
	}

	private IdentifierExpressionNode findArrayReference(
			OperatorNode operatorNode) {
		Operator operator = operatorNode.getOperator();

		if (operator == Operator.SUBSCRIPT) {
			ExpressionNode array = operatorNode.getArgument(0);

			if (array instanceof IdentifierExpressionNode)
				return (IdentifierExpressionNode) array;
			return null;
		} else {
			int num = operatorNode.numChildren();

			for (int i = 0; i < num; i++) {
				ASTNode child = operatorNode.child(i);

				if (child instanceof OperatorNode) {
					IdentifierExpressionNode result = findArrayReference(
							(OperatorNode) child);

					if (result != null)
						return result;
				}
			}
		}
		return null;
	}

	private ExpressionNode transformBigValueNode(ExpressionNode bigValueNode)
			throws SyntaxException {
		if (bigValueNode instanceof IntegerConstantNode) {
			ExpressionNode newArg = this.factorNewInputVariable(
					this.getIntValue((IntegerConstantNode) bigValueNode),
					false);

			return newArg;
		} else if (bigValueNode instanceof OperatorNode) {
			OperatorNode upperOperator = (OperatorNode) bigValueNode;
			Operator operator = upperOperator.getOperator();

			if (operator == Operator.DIV) {
				ExpressionNode numerator = upperOperator.getArgument(0);
				ExpressionNode newNumerator = this
						.transformBigValueNode(numerator);

				if (newNumerator != null)
					upperOperator.setArgument(0, newNumerator);
			}
			return null;
		} else if (bigValueNode instanceof IdentifierExpressionNode) {
			String identifer = ((IdentifierExpressionNode) bigValueNode)
					.getIdentifier().name();

			// for(; i<N; ), and N is initialized with some big
			// number
			if (this.variableNamesIntializedBig.containsKey(identifer)) {
				int value = this.variableNamesIntializedBig.get(identifer);
				ExpressionNode newInit = null;

				// update the declaration of N to be: int
				// N=_svcomp_unppk_scale;
				newInit = this.getDownScaledExpression(bigValueNode.getSource(),
						value);
				if (newInit == null) {
					// create new scale variable for N
					newInit = this.factorNewInputVariable(value, false);
				}
				this.variablesIntializedBig.get(identifer)
						.setInitializer(newInit);
				variableNamesIntializedBig.remove(identifer);
				variablesIntializedBig.remove(identifer);
			}
			return null;
		}
		return null;
	}

	/**
	 * checks if the given node is a declaration from stdlib.h.
	 * 
	 * This method assumes that only exit and abort are used in svcomp
	 * benchmarks. If more functions are used, they need to be added here.
	 * 
	 * @param node
	 *            the node to be checked
	 * @return true iff the given node is a declaration from stdlib.h
	 */
	private boolean isStdlibNode(BlockItemNode node) {
		// if (item.getSource().getFirstToken().getFormation() instanceof
		// Inclusion)
		// return false;
		if (node instanceof FunctionDeclarationNode) {
			FunctionDeclarationNode functionDecl = (FunctionDeclarationNode) node;
			String name = functionDecl.getName();

			if (name.equals(EXIT) || name.equals(ABORT)) {
				this.needsStdlibHeader = true;
				return true;
			}
		}
		return false;
	}

	/**
	 * checks if the given node is a declaration from string.h.
	 * 
	 * This method assumes that only exit and abort are used in svcomp
	 * benchmarks. If more functions are used, they need to be added here.
	 * 
	 * @param node
	 *            the node to be checked
	 * @return true iff the given node is a declaration from stdlib.h
	 */
	private boolean isStringNode(BlockItemNode node) {
		if (node instanceof FunctionDeclarationNode) {
			FunctionDeclarationNode functionDecl = (FunctionDeclarationNode) node;
			String name = functionDecl.getName();

			if (name.equals(STRCPY)) {
				this.needsStringHeader = true;
				return true;
			}
		}
		return false;
	}

	/**
	 * Removed any node in the root scope that satisfies at least one of the
	 * following:
	 * <ul>
	 * <li>struct definition in the form: <code>struct _IO_...</code>;</li>
	 * <li>variable declaration of the type <code>struct (_IO_...)*</code></li>
	 * </ul>
	 * 
	 * 
	 * <code>typedef SOME_TYPE pthread_*</code>. i.e., the identifier starts
	 * with "pthread_".
	 * 
	 * @param node
	 */
	private boolean isQualifiedIoNode(BlockItemNode node) {
		boolean toRemove = false;

		if (node instanceof TypedefDeclarationNode) {
			toRemove = isStructOrUnionOfIO(
					((TypedefDeclarationNode) node).getTypeNode());
		} else if (node instanceof StructureOrUnionTypeNode) {
			toRemove = isStructOrUnionOfIO((StructureOrUnionTypeNode) node);
		} else if (node instanceof VariableDeclarationNode) {
			TypeNode type = ((VariableDeclarationNode) node).getTypeNode();

			if (type instanceof PointerTypeNode) {
				toRemove = this.isStructOrUnionOfIO(
						((PointerTypeNode) type).referencedType());
			}
		} else if (node instanceof FunctionDeclarationNode) {
			if (((FunctionDeclarationNode) node).getName().equals(PRINTF))
				toRemove = true;
		}
		if (toRemove) {
			this.needsIoHeader = true;
		}
		return toRemove;
	}

	/**
	 * returns true iff the given type node is a struct or union type which has
	 * the tag starting with _IO_
	 * 
	 * @param typeNode
	 * @return
	 */
	private boolean isStructOrUnionOfIO(TypeNode typeNode) {
		if (typeNode instanceof StructureOrUnionTypeNode) {
			StructureOrUnionTypeNode structOrUnion = (StructureOrUnionTypeNode) typeNode;

			if (structOrUnion.getName().startsWith(IO_PREFIX))
				return true;
		}
		return false;
	}

	/**
	 * Removed any typedef declaration node in the root scope that has the form:
	 * <code>typedef SOME_TYPE pthread_*</code>. i.e., the identifier starts
	 * with "pthread_".
	 * 
	 * @param root
	 */
	private boolean isQualifiedPthreadNode(BlockItemNode item) {
		// if (item.getSource().getFirstToken().getFormation() instanceof
		// Inclusion)
		// return false;
		if (item instanceof TypedefDeclarationNode) {
			TypedefDeclarationNode typedef = (TypedefDeclarationNode) item;

			if (typedef.getName().startsWith(PTHREAD_PREFIX)) {
				needsPthreadHeader = true;
				return true;
			}
		} else if (item instanceof StructureOrUnionTypeNode) {
			StructureOrUnionTypeNode structOrUnion = (StructureOrUnionTypeNode) item;

			if (structOrUnion.getName().startsWith(PTHREAD_PREFIX)) {
				needsPthreadHeader = true;
				return true;
			}
		} else if (item instanceof FunctionDeclarationNode) {
			FunctionDeclarationNode functionDecl = (FunctionDeclarationNode) item;

			if (functionDecl.getName().startsWith(PTHREAD_PREFIX)) {
				needsPthreadHeader = true;
				return true;
			}
		}
		return false;
	}
}
