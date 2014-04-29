package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import edu.udel.cis.vsl.abc.ABCUnsupportedException;
import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.StringLiteralNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ExpressionStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ReturnNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.value.IF.StringValue;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.transform.IF.BaseTransformer;

/**
 * The IO transformer transforms<br>
 * <ul>
 * <li>all function calls printf(...) into frpintf(stdout, ...)</li>
 * <li>all function calls scanf(...) into fscanf(stdin, ...)</li>
 * <li>all function calls fopen(...) into $fopen(...)</li>
 * </ul>
 * 
 * @author zmanchun
 * 
 */
public class IOTransformer extends BaseTransformer {

	/* ************************** Public Static Fields *********************** */
	/**
	 * The code (short name) of this transformer.
	 */
	public static String CODE = "io";

	/**
	 * The long name of the transformer.
	 */
	public static String LONG_NAME = "IOTransformer";

	/**
	 * The description of this transformer.
	 */
	public static String SHORT_DESCRIPTION = "transforms C program with IO to CIVL-C";

	/* ************************** Private Static Fields ********************** */
	/**
	 * The name of printf function.
	 */
	private static String PRINTF = "printf";

	/**
	 * The name of fprintf function.
	 */
	private static String FPRINTF = "fprintf";

	/**
	 * The name of scanf function.
	 */
	private static String SCANF = "scanf";

	/**
	 * The name of fscanf function.
	 */
	private static String FSCANF = "fscanf";

	/**
	 * The name of fopen function.
	 */
	private static String FOPEN = "fopen";

	/**
	 * The name of $fopen function (CIVL's stdio implementation).
	 */
	private static String FOPEN_NEW = "$fopen";

	/**
	 * The representation of the 16 modes of opening a file in CIVL.
	 */
	private static String CIVL_FILE_MODE_R = "CIVL_FILE_MODE_R";// r
	private static String CIVL_FILE_MODE_W = "CIVL_FILE_MODE_W";// w
	private static String CIVL_FILE_MODE_WX = "CIVL_FILE_MODE_WX";// wx
	private static String CIVL_FILE_MODE_A = "CIVL_FILE_MODE_A";// a
	private static String CIVL_FILE_MODE_RB = "CIVL_FILE_MODE_RB";// rb
	private static String CIVL_FILE_MODE_WB = "CIVL_FILE_MODE_WB";// wb
	private static String CIVL_FILE_MODE_WBX = "CIVL_FILE_MODE_WBX";// wbx
	private static String CIVL_FILE_MODE_AB = "CIVL_FILE_MODE_AB";// ab
	private static String CIVL_FILE_MODE_RP = "CIVL_FILE_MODE_RP";// r+
	private static String CIVL_FILE_MODE_WP = "CIVL_FILE_MODE_WP";// w+
	private static String CIVL_FILE_MODE_WPX = "CIVL_FILE_MODE_WPX";// w+x
	private static String CIVL_FILE_MODE_AP = "CIVL_FILE_MODE_AP";// a+
	private static String CIVL_FILE_MODE_RPB = "CIVL_FILE_MODE_RPB";// r+b or rb+
	private static String CIVL_FILE_MODE_WPB = "CIVL_FILE_MODE_WPB";// w+b or wb+
	private static String CIVL_FILE_MODE_WPBX = "CIVL_FILE_MODE_WPBX";// w+bx or
																		// wb+x
	private static String CIVL_FILE_MODE_APB = "CIVL_FILE_MODE_APB";// a+b or ab+

	/**
	 * The string representation of the 16 modes of opening of a file in C.
	 */
	private static String FOPEN_R = "r";
	private static String FOPEN_W = "w";
	private static String FOPEN_WX = "wx";
	private static String FOPEN_A = "a";
	private static String FOPEN_RB = "rb";
	private static String FOPEN_WB = "wb";
	private static String FOPEN_WBX = "wbx";
	private static String FOPEN_AB = "ab";
	private static String FOPEN_RP = "r+";
	private static String FOPEN_WP = "w+";
	private static String FOPEN_WPX = "w+x";
	private static String FOPEN_AP = "a+";
	private static String FOPEN_RPB = "r+b";
	private static String FOPEN_RBP = "rb+";
	private static String FOPEN_WPB = "w+b";
	private static String FOPEN_WBP = "wb+";
	private static String FOPEN_WPBX = "w+bx";
	private static String FOPEN_WBPX = "wb+x";
	private static String FOPEN_APB = "a+b";
	private static String FOPEN_ABP = "ab+";

	/**
	 * The CIVL system function to destroy a file system.
	 */
	private static String FILESYSTEM_DESTROY = "$filesystem_destroy";

	/**
	 * The CIVL system function to copy all files of a file system to an array.
	 */
	private static String FILESYSTEM_COPY_OUTPUT = "$filesystem_copy_output";

	/**
	 * The CIVL system function to destroy a memory unit through a pointer.
	 */
	private static String FREE = "$free";

	/**
	 * The name of the default file system in the root scope.
	 */
	private static String CIVL_FILESYSTEM = "CIVL_filesystem";

	/**
	 * The name of the output array of files.
	 */
	private static String CIVL_OUTPUT_FILESYSTEM = "CIVL_output_filesystem";

	/**
	 * The name of stdin.
	 */
	private static String STDIN = "stdin";
	/**
	 * The name of stdout.
	 */
	private static String STDOUT = "stdout";
	/**
	 * The name of stderr.
	 */
	private static String STDERR = "stderr";

	/* ****************************** Constructor ************************** */

	public IOTransformer(ASTFactory astFactory) {
		super(IOTransformer.CODE, IOTransformer.LONG_NAME,
				IOTransformer.SHORT_DESCRIPTION, astFactory);
	}
	
	/* *************************** Private Methods ************************* */

	

	private void processFreeCall(ASTNode node) throws SyntaxException {
		int numChildren = node.numChildren();

		for (int i = 0; i < numChildren; i++) {
			ASTNode child = node.child(i);

			if (child instanceof FunctionDefinitionNode) {
				FunctionDefinitionNode function = (FunctionDefinitionNode) child;
				String functionName = function.getName();

				if (functionName.equals("main")) {
					List<BlockItemNode> finalCalls = new ArrayList<>();
					Source source = node.getSource();
					List<StatementNode> freeStatements = this.freeCalls(node
							.getSource());
					CompoundStatementNode body = function.getBody();
					BlockItemNode lastStatement = body.getSequenceChild(body
							.numChildren() - 1);
					StatementNode finalStatements;

					finalCalls.add(this.copyFilesToOutput(source));
					finalCalls.addAll(freeStatements);
					finalStatements = nodeFactory.newCompoundStatementNode(
							source, finalCalls);
					if (!(lastStatement instanceof ReturnNode)) {
						body.addSequenceChild(finalStatements.copy());
					}
					this.addFreeBeforeReturn(body, finalStatements);
				}
			}
		}
	}

	private StatementNode copyFilesToOutput(Source source) {
		ExpressionNode civlFileSystem = nodeFactory
				.newIdentifierExpressionNode(source,
						nodeFactory.newIdentifierNode(source, CIVL_FILESYSTEM));
		ExpressionNode outputArray = nodeFactory.newIdentifierExpressionNode(
				source,
				nodeFactory.newIdentifierNode(source, CIVL_OUTPUT_FILESYSTEM));
		FunctionCallNode copyCall = nodeFactory.newFunctionCallNode(source,
				nodeFactory.newIdentifierExpressionNode(source, nodeFactory
						.newIdentifierNode(source, FILESYSTEM_COPY_OUTPUT)),
				Arrays.asList(civlFileSystem, outputArray), null);

		return nodeFactory.newExpressionStatementNode(copyCall);
	}

	private List<StatementNode> freeCalls(Source source) throws SyntaxException {
		ExpressionStatementNode freeFilesystemStatement, freeStdoutStatement, freeStdinStatement, freeStderrStatement;
		StatementNode ifStdoutStatement, ifStdinStatement, ifStderrStatement;
		FunctionCallNode freeFilesystem, freeStdout, freeStdin, freeStderr;
		ExpressionNode condition;
		ExpressionNode argument = nodeFactory.newIdentifierExpressionNode(
				source, nodeFactory.newIdentifierNode(source, CIVL_FILESYSTEM));
		ExpressionNode nullPointer;

		freeFilesystem = nodeFactory.newFunctionCallNode(source, nodeFactory
				.newIdentifierExpressionNode(source, nodeFactory
						.newIdentifierNode(source, FILESYSTEM_DESTROY)), Arrays
				.asList(argument), null);
		freeFilesystemStatement = nodeFactory
				.newExpressionStatementNode(freeFilesystem);
		argument = nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, STDOUT));
		freeStdout = nodeFactory.newFunctionCallNode(
				source,
				nodeFactory.newIdentifierExpressionNode(source,
						nodeFactory.newIdentifierNode(source, FREE)),
				Arrays.asList(argument), null);
		freeStdoutStatement = nodeFactory
				.newExpressionStatementNode(freeStdout);
		nullPointer = nodeFactory.newCastNode(
				source,
				nodeFactory.newPointerTypeNode(source,
						nodeFactory.newVoidTypeNode(source), null),
				nodeFactory.newIntegerConstantNode(source, "0"));
		condition = nodeFactory.newOperatorNode(source, Operator.NEQ,
				Arrays.asList(argument.copy(), nullPointer));
		ifStdoutStatement = nodeFactory.newIfNode(source, condition,
				freeStdoutStatement);
		argument = nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, STDIN));
		freeStdin = nodeFactory.newFunctionCallNode(
				source,
				nodeFactory.newIdentifierExpressionNode(source,
						nodeFactory.newIdentifierNode(source, FREE)),
				Arrays.asList(argument), null);
		freeStdinStatement = nodeFactory.newExpressionStatementNode(freeStdin);
		condition = nodeFactory.newOperatorNode(source, Operator.NEQ,
				Arrays.asList(argument.copy(), nullPointer.copy()));
		ifStdinStatement = nodeFactory.newIfNode(source, condition,
				freeStdinStatement);
		argument = nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, STDERR));
		freeStderr = nodeFactory.newFunctionCallNode(
				source,
				nodeFactory.newIdentifierExpressionNode(source,
						nodeFactory.newIdentifierNode(source, FREE)),
				Arrays.asList(argument), null);
		freeStderrStatement = nodeFactory
				.newExpressionStatementNode(freeStderr);
		condition = nodeFactory.newOperatorNode(source, Operator.NEQ,
				Arrays.asList(argument.copy(), nullPointer.copy()));
		ifStderrStatement = nodeFactory.newIfNode(source, condition,
				freeStderrStatement);
		return Arrays.asList(freeFilesystemStatement, ifStdoutStatement,
				ifStdinStatement, ifStderrStatement);
	}

	/**
	 * Processes an AST node.
	 * 
	 * @param node
	 * @throws SyntaxException
	 */
	private void renameFunctionCalls(ASTNode node) throws SyntaxException {
		int numChildren = node.numChildren();

		for (int i = 0; i < numChildren; i++) {
			ASTNode child = node.child(i);

			if (child != null)
				this.renameFunctionCalls(node.child(i));
		}
		if (node instanceof FunctionCallNode) {
			this.processFunctionCall((FunctionCallNode) node);
		}
	}

	private void addFreeBeforeReturn(ASTNode node,
			StatementNode functionCallStatement) {
		int numChildren = node.numChildren();

		for (int i = 0; i < numChildren; i++) {
			ASTNode child = node.child(i);

			if (child == null)
				continue;
			if (child instanceof ReturnNode) {
				List<BlockItemNode> statements = new ArrayList<>(2);

				statements.add(functionCallStatement.copy());
				statements.add((ReturnNode) child);
				node.removeChild(i);
				node.setChild(i, nodeFactory.newCompoundStatementNode(
						child.getSource(), statements));
			} else
				this.addFreeBeforeReturn(node.child(i), functionCallStatement);
		}
	}

	private void processFunctionCall(FunctionCallNode functionCall)
			throws SyntaxException {
		if (functionCall.getFunction().expressionKind() == ExpressionKind.IDENTIFIER_EXPRESSION) {
			IdentifierExpressionNode functionExpression = (IdentifierExpressionNode) functionCall
					.getFunction();
			String functionName = functionExpression.getIdentifier().name();
			String firstArgName = "";
			IdentifierNode functionNameIdentifer = functionExpression
					.getIdentifier();

			if (functionName.equals(PRINTF) || functionName.equals(SCANF)) {
				if (functionName.equals(PRINTF)) {
					functionNameIdentifer.setName(FPRINTF);
					firstArgName = STDOUT;
				} else if (functionName.equals(SCANF)) {
					functionNameIdentifer.setName(FSCANF);
					firstArgName = STDIN;
				}
				processPrintfOrScanf(functionCall, firstArgName);
			} else if (functionName.equals(FOPEN)) {
				functionNameIdentifer.setName(FOPEN_NEW);
				processFopen(functionCall);
			}
		}
	}

	/**
	 * fopen(filename, "mode") --> $fopen(CIVL_filesystem, filename,
	 * MODE_CONSTANT)
	 * 
	 * @param functionCall
	 * @throws SyntaxException
	 */
	private void processFopen(FunctionCallNode functionCall)
			throws SyntaxException {
		Source source = functionCall.getFunction().getSource();
		IdentifierExpressionNode civlFileSystem = nodeFactory
				.newIdentifierExpressionNode(source,
						nodeFactory.newIdentifierNode(source, CIVL_FILESYSTEM));
		int oldCount = functionCall.getNumberOfArguments();
		List<ExpressionNode> arguments = new ArrayList<>(oldCount + 1);
		ExpressionNode modeArg = functionCall.getArgument(1);

		arguments.add(civlFileSystem);
		arguments.add(functionCall.getArgument(0));
		if (modeArg instanceof StringLiteralNode) {
			StringValue value = ((StringLiteralNode) modeArg)
					.getConstantValue();
			String modeString = this.processFopenMode(value.toString(),
					modeArg.getSource());

			source = modeArg.getSource();
			arguments.add(nodeFactory.newIdentifierExpressionNode(source,
					nodeFactory.newIdentifierNode(source, modeString)));
		} else {
			throw new ABCUnsupportedException(
					"non-string-literal file mode of fopen");
		}
		for (int i = 0; i < oldCount; i++) {
			ExpressionNode argument = functionCall.getArgument(i);

			argument.parent().removeChild(argument.childIndex());
		}
		functionCall.setChild(1, nodeFactory.newSequenceNode(source,
				"ActualParameterList", arguments));
	}

	private String processFopenMode(String mode, Source source)
			throws SyntaxException {
		if (mode.equals(FOPEN_R))
			return CIVL_FILE_MODE_R;
		if (mode.equals(FOPEN_W))
			return CIVL_FILE_MODE_W;
		if (mode.equals(FOPEN_WX))
			return CIVL_FILE_MODE_WX;
		if (mode.equals(FOPEN_A))
			return CIVL_FILE_MODE_A;
		if (mode.equals(FOPEN_RB))
			return CIVL_FILE_MODE_RB;
		if (mode.equals(FOPEN_WB))
			return CIVL_FILE_MODE_WB;
		if (mode.equals(FOPEN_WBX))
			return CIVL_FILE_MODE_WBX;
		if (mode.equals(FOPEN_AB))
			return CIVL_FILE_MODE_AB;
		if (mode.equals(FOPEN_RP))
			return CIVL_FILE_MODE_RP;
		if (mode.equals(FOPEN_WP))
			return CIVL_FILE_MODE_WP;
		if (mode.equals(FOPEN_WPX))
			return CIVL_FILE_MODE_WPX;
		if (mode.equals(FOPEN_AP))
			return CIVL_FILE_MODE_AP;
		if (mode.equals(FOPEN_RPB) || mode.equals(FOPEN_RBP))
			return CIVL_FILE_MODE_RPB;
		if (mode.equals(FOPEN_WPB) || mode.equals(FOPEN_WBP))
			return CIVL_FILE_MODE_WPB;
		if (mode.equals(FOPEN_WPBX) || mode.equals(FOPEN_WBPX))
			return CIVL_FILE_MODE_WPBX;
		if (mode.equals(FOPEN_APB) || mode.equals(FOPEN_ABP))
			return CIVL_FILE_MODE_APB;
		throw new SyntaxException("Invalid mode " + mode + " of fopen.", source);
	}

	private void processPrintfOrScanf(FunctionCallNode functionCall,
			String firstArgName) {
		Source source = functionCall.getFunction().getSource();
		IdentifierExpressionNode firstArg = nodeFactory
				.newIdentifierExpressionNode(source,
						nodeFactory.newIdentifierNode(source, firstArgName));
		int oldCount = functionCall.getNumberOfArguments();
		List<ExpressionNode> arguments = new ArrayList<>(oldCount + 1);

		arguments.add(firstArg);
		for (int i = 0; i < oldCount; i++) {
			ExpressionNode argument = functionCall.getArgument(i);

			argument.parent().removeChild(argument.childIndex());
			arguments.add(argument);
		}
		functionCall.setChild(1, nodeFactory.newSequenceNode(source,
				"ActualParameterList", arguments));
	}
	
	/* ********************* Methods From BaseTransformer ****************** */
	
	@Override
	public AST transform(AST unit) throws SyntaxException {
		ASTNode rootNode = unit.getRootNode();

		assert this.astFactory == unit.getASTFactory();
		assert this.nodeFactory == astFactory.getNodeFactory();
		unit.release();
		this.renameFunctionCalls(rootNode);
		this.processFreeCall(rootNode);
		return astFactory.newTranslationUnit(rootNode);
	}

}
