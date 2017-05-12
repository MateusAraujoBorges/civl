package edu.udel.cis.vsl.civl.semantics.common;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.mpi.LibmpiEvaluator;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.AbstractFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.model.IF.CIVLTypeFactory;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.SystemFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.AbstractFunctionCallExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.AddressOfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ArrayLambdaExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ArrayLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.BooleanLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.CastExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.CharLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DereferenceExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DerivativeCallExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DomainGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DotExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DynamicTypeOfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression.ExpressionKind;
import edu.udel.cis.vsl.civl.model.IF.expression.ExtendedQuantifiedExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionCallExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionIdentifierExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.HereOrRootExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.InitialValueExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.IntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LambdaExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.MPIContractExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ProcnullExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RealLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RecDomainLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RegularRangeExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ScopeofExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SelfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofTypeExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.StateExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.StructOrUnionLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SubscriptExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SystemGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLBundleType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLCompleteArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLCompleteDomainType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLDomainType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLEnumType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLFunctionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType.PrimitiveTypeKind;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType.TypeKind;
import edu.udel.cis.vsl.civl.model.IF.type.StructOrUnionField;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryLoaderException;
import edu.udel.cis.vsl.civl.semantics.IF.MemoryUnitExpressionEvaluator;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.semantics.IF.TypeEvaluation;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnitFactory;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.civl.util.IF.Singleton;
import edu.udel.cis.vsl.civl.util.IF.Triple;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.OffsetReference;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.expr.TupleComponentReference;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicSequence;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicFunctionType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType.SymbolicTypeKind;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;
import edu.udel.cis.vsl.sarl.expr.cnf.BooleanPrimitive;
import edu.udel.cis.vsl.sarl.number.IF.Numbers;

/**
 * An evaluator is used to evaluate expressions.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class CommonEvaluator implements Evaluator {

	private static int INTEGER_BIT_LENGTH = 32;
	private static String ABSTRACT_FUNCTION_PREFIX = "_uf_";
	public static String POINTER_TO_INT_FUNCTION = "_pointer2Int";
	public static String INT_TO_POINTER_FUNCTION = "_int2Pointer";
	public static String CHAR_TO_INT_FUNCTION = "_char2int";
	public static String INT_TO_CHAR_FUNCTION = "_int2char";
	/**
	 * An abstract function which shall represent a dereference operation, in
	 * the context where pure first-order logic is applied, when the operation
	 * possibly results to an undefined value in C language.
	 */
	public static String TOTAL_DEREFERENCE_FUNCTION = "_total_deref";

	/* *************************** Instance Fields ************************* */
	protected LibraryExecutorLoader libExeLoader;

	protected MemoryUnitFactory memUnitFactory;

	protected CIVLConfiguration civlConfig;

	/**
	 * The library evaluator loader. This is used to location and obtain the
	 * appropriate library evaluators when library-defined expressions need to
	 * be evaluated. These are primarily guards of system functions.
	 */
	protected LibraryEvaluatorLoader libLoader;

	/**
	 * An uninterpreted function used to evaluate "BigO" of an expression. It
	 * takes as input one expression of real type and return a real type,
	 * <code>real $O(real x)</code>.
	 */
	private SymbolicExpression bigOFunction;

	/**
	 * The dynamic heap type. This is the symbolic type of a symbolic expression
	 * which represents the value of an entire heap. It is a tuple in which
	 * there is one component for each <code>malloc</code> statement in a CIVL
	 * model. A component of such a tuple is used to represent all the object
	 * allocated by the corresponding <code>malloc</code> statement. Such a
	 * component has type "array of array of T", where T is the type that occurs
	 * as in an expression of the form <code>(T*)malloc(n*sizeof(T))</code>.
	 */
	private SymbolicTupleType heapType;

	/**
	 * The identity reference expression. A symbolic reference expression can be
	 * viewed as a function which takes a symbolic expression x (of the
	 * appropriate type) and returns a sub-expression of x. The identify
	 * reference, viewed this way, corresponds to the identify function: given x
	 * it returns x.
	 */
	private ReferenceExpression identityReference;

	/**
	 * The unique model factory used to construct the CIVL model elements that
	 * this evaluator will encounter.
	 */
	protected ModelFactory modelFactory;

	/**
	 * The symbolic expression representing "NULL" expression, which is non-null
	 * (as a Java object) but represents the absence of some value. It is used
	 * in CIVL to represent the undefined value: it is the value assigned to
	 * variables before they are initialized. Note that this is the only
	 * symbolic expression that does not have a type.
	 */
	private SymbolicExpression nullExpression;

	/**
	 * The unique real number factory used in the system.
	 */
	private NumberFactory numberFactory = Numbers.REAL_FACTORY;

	/**
	 * The symbolic expression 1 of integer type. (Note that this is distinct
	 * from the 1 of real type.)
	 */
	protected NumericExpression one;

	/**
	 * The pointer value is a triple <s,v,r> where s identifies the dynamic
	 * scope, v identifies the variable within that scope, and r identifies a
	 * point within that variable. The type of s is scopeType, which is just a
	 * tuple wrapping a single integer which is the dynamic scope ID number. The
	 * type of v is integer; it is the (static) variable ID number for the
	 * variable in its scope. The type of r is ReferenceExpression from SARL.
	 */
	protected SymbolicTupleType pointerType;

	/**
	 * The function pointer value is a pair <s,i> where s identifies the dynamic
	 * scope, i is the function id in the scope. The type of s is scopeType,
	 * which is just a tuple wrapping a single integer which is the dynamic
	 * scope ID number. The type of i is integer. Function pointer type need to
	 * be different from pointer type, because there is analysis particularly
	 * for pointers, like heap object reachability, reachable memory units, etc.
	 */
	private SymbolicTupleType functionPointerType;

	/**
	 * An uninterpreted function used to evaluate "sizeof" on a type. It takes
	 * as input one expression of type dynamicType and returns an integer
	 * expression.
	 */
	private SymbolicExpression sizeofFunction;

	/**
	 * The unique state factory used in the system.
	 */
	protected StateFactory stateFactory;

	/**
	 * The unique symbolic universe used in the system.
	 */
	protected SymbolicUniverse universe;

	/**
	 * The symbolic int object of 0.
	 */
	private IntObject zeroObj;

	/**
	 * The symbolic int object of 2.
	 */
	private IntObject twoObj;

	/**
	 * The symbolic numeric expression of 0 of integer type.
	 */
	protected NumericExpression zero;

	/**
	 * The symbolic numeric expression of 0 of real type.
	 */
	private NumericExpression zeroR;

	/** The SARL character type. */
	private SymbolicType charType;

	/**
	 * The SARL character 0, i.e., '\0' or '\u0000', used as the "null character
	 * constant" in C.
	 */
	private SymbolicExpression nullCharExpr;

	/**
	 * The symbolic utility for manipulations of symbolic expressions.
	 */
	protected SymbolicUtility symbolicUtil;

	/**
	 * The error logger to report errors.
	 */
	protected CIVLErrorLogger errorLogger;

	/**
	 * The symbolic numeric expression that has the value of either zero or one.
	 */
	// private NumericExpression zeroOrOne;

	/**
	 * The symbolic analyzer to be used.
	 */
	protected SymbolicAnalyzer symbolicAnalyzer;

	protected MemoryUnitExpressionEvaluator memUnitEvaluator;

	protected CIVLTypeFactory typeFactory;

	// private SymbolicConstant pointer2IntFunc;
	//
	// private SymbolicConstant int2PointerFunc;

	private UFExtender char2IntCaster;

	private UFExtender int2CharCaster;
	private UFExtender pointer2IntCaster;
	private UFExtender int2PointerCaster;

	/**
	 * A bit-vector type which representing a boolean array with a concrete
	 * length corresponding to the bit-length of an integer define by the
	 * environment. (The default length is 32);
	 */
	@SuppressWarnings("unused")
	private SymbolicCompleteArrayType bitVectorType;

	private FunctionCallExecutor functionCallExecutor;

	private SymbolicExpression offsetFunction;

	/* ***************************** Constructors ************************** */

	/**
	 * Create a new instance of evaluator for evaluating expressions.
	 * 
	 * @param modelFactory
	 *            The model factory of the system.
	 * @param stateFactory
	 *            The state factory of the system.
	 * @param loader
	 *            The loader for library evaluators.
	 * @param symbolicUtil
	 *            The symbolic utility.
	 * @param symbolicAnalyzer
	 *            The symbolic analyzer used in the system.
	 * @param errorLogger
	 *            The error logger for logging errors.
	 */
	public CommonEvaluator(ModelFactory modelFactory, StateFactory stateFactory,
			LibraryEvaluatorLoader loader, LibraryExecutorLoader loaderExec,
			SymbolicUtility symbolicUtil, SymbolicAnalyzer symbolicAnalyzer,
			MemoryUnitFactory memUnitFactory, CIVLErrorLogger errorLogger,
			CIVLConfiguration config) {
		this.libExeLoader = loaderExec;
		this.memUnitFactory = memUnitFactory;
		this.libLoader = loader;
		this.errorLogger = errorLogger;
		this.symbolicUtil = symbolicUtil;
		this.symbolicAnalyzer = symbolicAnalyzer;
		((CommonSymbolicAnalyzer) symbolicAnalyzer).setEvaluator(this);
		this.modelFactory = modelFactory;
		this.typeFactory = modelFactory.typeFactory();
		this.stateFactory = stateFactory;
		this.universe = stateFactory.symbolicUniverse();
		this.memUnitEvaluator = new CommonMemoryUnitEvaluator(symbolicUtil,
				this, memUnitFactory, universe);
		pointerType = typeFactory.pointerSymbolicType();
		functionPointerType = typeFactory.functionPointerSymbolicType();
		heapType = typeFactory.heapSymbolicType();
		zeroObj = (IntObject) universe.canonic(universe.intObject(0));
		twoObj = (IntObject) universe.canonic(universe.intObject(2));
		identityReference = (ReferenceExpression) universe
				.canonic(universe.identityReference());
		zero = (NumericExpression) universe.canonic(universe.integer(0));
		zeroR = (NumericExpression) universe.canonic(universe.zeroReal());
		one = (NumericExpression) universe.canonic(universe.integer(1));
		nullExpression = universe.nullExpression();
		sizeofFunction = symbolicUtil.sizeofFunction();
		bigOFunction = universe.symbolicConstant(universe.stringObject("BIG_O"),
				universe.functionType(
						new Singleton<SymbolicType>(universe.realType()),
						universe.realType()));
		bigOFunction = universe.canonic(bigOFunction);
		offsetFunction = universe.symbolicConstant(
				universe.stringObject("OFFSET"),
				universe.functionType(
						Arrays.asList(symbolicUtil.dynamicType(),
								universe.integerType()),
						universe.integerType()));
		offsetFunction = universe.canonic(offsetFunction);
		charType = universe.characterType();
		nullCharExpr = universe.canonic(universe.character('\u0000'));
		// pointer2IntFunc = universe.symbolicConstant(universe
		// .stringObject(POINTER_TO_INT_FUNCTION), universe.functionType(
		// Arrays.asList(this.pointerType), this.universe.integerType()));
		// int2PointerFunc = universe.symbolicConstant(universe
		// .stringObject(INT_TO_POINTER_FUNCTION), universe.functionType(
		// Arrays.asList(this.universe.integerType()), this.pointerType));
		this.char2IntCaster = new UFExtender(this.universe,
				CHAR_TO_INT_FUNCTION, charType, universe.integerType(),
				new Char2IntCaster(this.universe, this.symbolicUtil));
		this.int2CharCaster = new UFExtender(this.universe,
				INT_TO_CHAR_FUNCTION, universe.integerType(), charType,
				new Int2CharCaster(this.universe, this.symbolicUtil));
		pointer2IntCaster = new UFExtender(this.universe,
				POINTER_TO_INT_FUNCTION, this.pointerType,
				universe.integerType(), new Pointer2IntCaster(universe,
						symbolicUtil, this.pointerType));
		int2PointerCaster = new UFExtender(this.universe,
				INT_TO_POINTER_FUNCTION, universe.integerType(),
				this.pointerType, new Int2PointerCaster(universe, symbolicUtil,
						this.pointerType));
		this.civlConfig = config;
		// this.zeroOrOne = (NumericExpression) universe.symbolicConstant(
		// universe.stringObject("ZeroOrOne"), universe.integerType());
		this.bitVectorType = universe.bitVectorType(INTEGER_BIT_LENGTH);
		this.functionCallExecutor = new FunctionCallExecutor(modelFactory,
				stateFactory, loaderExec, this, symbolicAnalyzer, errorLogger,
				civlConfig);
	}

	/* ************************** Private Methods ************************** */

	/**
	 * Dereferences a pointer. Logs error when the dereference fails, like when
	 * the pointer is null.
	 * 
	 * @param source
	 *            Source code information for error report.
	 * @param state
	 *            The state where the dereference happens.
	 * @param process
	 *            The process name for error report.
	 * @param referredType
	 *            The {@link CIVLType} of the dereference operation.
	 * @param pointer
	 *            The pointer to be dereferenced.
	 * @param checkOutput
	 *            Is reading of output variable to be checked?
	 * @param analysisOnly
	 *            Is this called from pointer reachability analysis?
	 * @param strict
	 *            Should the method report undefined value error when the value
	 *            pointed by the pointer is undefined ? Currently, this filed is
	 *            false only when executing $copy function.
	 * @param muteErrorSideEffects
	 *            Should this method mute error side-effects ? i.e.
	 *            Dereferencing a pointer with error side-effects <strong>
	 *            results an undefined value of the same type as the dereference
	 *            expression </strong> iff this parameter set to true.
	 *            Otherwise, an error will be reported and
	 *            UnsatisfiablePathConditionException will be thrown.
	 * @return A possibly new state and the value of memory space pointed by the
	 *         pointer.
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation dereferenceWorker(CIVLSource source, State state,
			String process, CIVLType referredType, SymbolicExpression pointer,
			boolean checkOutput, boolean analysisOnly, boolean strict,
			boolean muteErrorSideEffects)
			throws UnsatisfiablePathConditionException {
		boolean throwPCException = false;
		SymbolicExpression deref;

		// C11 6.5.3.2: If an invalid value has been assigned to the
		// pointer, the behavior of the unary * operator is undefined.
		//
		// footnote: Among the invalid values for dereferencing a pointer by
		// the unary * operator are a null pointer, an address
		// inappropriately aligned for the type of object pointed to, and
		// the address of an object after the end of its lifetime.
		deref = dereferenceWorkerErrorChecking(state, process, referredType,
				pointer, muteErrorSideEffects, source);
		assert deref == null || muteErrorSideEffects;
		if (deref != null)
			return new Evaluation(state, deref);
		else {
			ReferenceExpression symRef = symbolicUtil.getSymRef(pointer);
			SymbolicExpression variableValue;
			int vid = symbolicUtil.getVariableId(source, pointer);
			int sid = symbolicUtil.getDyscopeId(source, pointer);

			if (sid == ModelConfiguration.DYNAMIC_CONSTANT_SCOPE) {
				variableValue = modelFactory.model().staticConstantScope()
						.variable(vid).constantValue();
			} else {
				if (!analysisOnly && checkOutput) {
					Variable variable = state.getDyscope(sid).lexicalScope()
							.variable(vid);

					if (variable.isOutput()) {
						errorLogger.logSimpleError(source, state, process,
								symbolicAnalyzer.stateInformation(state),
								ErrorKind.OUTPUT_READ,
								"Attempt to read output variable "
										+ variable.name().name());
						throwPCException = true;
					}
				}
				variableValue = state.getDyscope(sid).getValue(vid);
			}
			if (variableValue.isNull() && strict && !muteErrorSideEffects) {
				errorLogger.logSimpleError(source, state, process,
						symbolicAnalyzer.stateInformation(state),
						ErrorKind.UNDEFINED_VALUE,
						"Attempt to dereference a pointer that refers "
								+ "to an object with undefined value");
				throwPCException = true;
			}
			try {
				deref = universe.dereference(variableValue, symRef);
			} catch (SARLException e) {
				if (muteErrorSideEffects) {
					deref = totalDereferenceFunction(referredType, pointer);
				} else
					errorLogger.logSimpleError(source, state, process,
							symbolicAnalyzer.stateInformation(state),
							ErrorKind.DEREFERENCE,
							"Illegal pointer dereference: " + e.getMessage()
									+ "\n"
									+ symbolicAnalyzer.stateInformation(state));
				throwPCException = true;
			}
		}
		if (throwPCException)
			throw new UnsatisfiablePathConditionException();
		else
			return new Evaluation(state, deref);
	}

	/**
	 * <p>
	 * Error checking for dereference operations. This method checks if the
	 * given pointer
	 * <li>has NOT a pointer type</li>
	 * <li>is NOT a concrete pointer</li>
	 * <li>is a NULL pointer</li>
	 * <li>points to a NOT exist dynamic scope</li> <br>
	 * If any the above cases happens, either an error will be logged or an
	 * undefined value will be returned.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The String identifier of the process
	 * @param pointer
	 *            The pointer to be dereferenced.
	 * @param muteErrorSideEffects
	 *            Should this method mute error side-effects ? i.e.
	 *            Dereferencing a pointer with error side-effects <strong>
	 *            results an undefined value of the same type as the dereference
	 *            expression </strong> iff this parameter set to true.
	 *            Otherwise, an error will be reported and
	 *            UnsatisfiablePathConditionException will be thrown.
	 * @param source
	 *            The {@link CIVLSource} associates with the dereference
	 *            operation.
	 * @return An undefined value iff the pointer falls into one of the error
	 *         cases and muteErrorSideEffects is true. Java-null iff
	 *         muteErrorSideEffects is false;
	 * @throws UnsatisfiablePathConditionException
	 *             When muteErrorSideEffects is false and the pointer falls into
	 *             one of the error cases.
	 */
	private SymbolicExpression dereferenceWorkerErrorChecking(State state,
			String process, CIVLType referredType, SymbolicExpression pointer,
			boolean muteErrorSideEffects, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		boolean throwPCException = false;

		if (pointer == symbolicUtil.undefinedPointer()
				|| !pointer.type().equals(pointerType)) {
			if (!muteErrorSideEffects)
				errorLogger.logSimpleError(source, state, process,
						this.symbolicAnalyzer.stateInformation(state),
						ErrorKind.UNDEFINED_VALUE,
						"attempt to deference an invalid pointer");
			throwPCException = true;
		} else if (pointer.operator() != SymbolicOperator.TUPLE) {
			if (!muteErrorSideEffects)
				errorLogger.logSimpleError(source, state, process,
						symbolicAnalyzer.stateInformation(state),
						ErrorKind.UNDEFINED_VALUE,
						"attempt to deference a pointer that is never initialized");
			throwPCException = true;
		} else if (symbolicUtil.isNullPointer(pointer)) {
			if (!muteErrorSideEffects)
				// null pointer dereference
				errorLogger.logSimpleError(source, state, process,
						this.symbolicAnalyzer.stateInformation(state),
						ErrorKind.DEREFERENCE,
						"attempt to deference a null pointer");
			throwPCException = true;
		} else {
			int sid = symbolicUtil.getDyscopeId(source, pointer);

			if (sid == ModelConfiguration.DYNAMIC_REMOVED_SCOPE) {
				if (!muteErrorSideEffects)
					errorLogger.logSimpleError(source, state, process,
							symbolicAnalyzer.stateInformation(state),
							ErrorKind.DEREFERENCE,
							"Attempt to dereference pointer into scope"
									+ " which has been removed from state: \n "
									+ symbolicAnalyzer
											.symbolicExpressionToString(source,
													state, null, pointer));
				throwPCException = true;
			}
		}
		if (throwPCException && muteErrorSideEffects)
			return totalDereferenceFunction(referredType, pointer);
		if (throwPCException)
			throw new UnsatisfiablePathConditionException();
		return null;
	}

	/**
	 * <p>
	 * <strong>Pre-condition:</strong> Dereferencing the given pointer results
	 * an undefined value.
	 * </p>
	 * 
	 * <p>
	 * Creates an abstract function to represent a dereference operation, which
	 * may results an undefined value in C language.
	 * </p>
	 * 
	 * @param referredType
	 *            The {@link CIVLType} of the dereferenced object
	 * @param pointer
	 *            The pointer which cannot be illegally dereferenced.
	 * @return An abstract function representing a pointer dereference.
	 */
	private SymbolicExpression totalDereferenceFunction(CIVLType referredType,
			SymbolicExpression pointer) {
		SymbolicExpression totoalFuction = universe.symbolicConstant(
				universe.stringObject(TOTAL_DEREFERENCE_FUNCTION),
				universe.functionType(
						Arrays.asList(typeFactory.pointerSymbolicType()),
						referredType.getDynamicType(universe)));

		return universe.apply(totoalFuction, Arrays.asList(pointer));
	}

	/**
	 * Evaluates the dynamic type of a given CIVL type at a certain state. When
	 * the CIVL type has some state, e.g., an array type with a variable as the
	 * extent, the type needs to be evaluated.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process where the computation happens.
	 * @param type
	 *            The CIVL type to be evaluated for the dynamic type.
	 * @param source
	 *            The source code element for error report.
	 * @param isDeclaration
	 *            The flag denoting if the type is part of a variable/function
	 *            declaration.
	 * @return The dynamic type of the given type.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation dynamicTypeOf(State state, int pid, CIVLType type,
			CIVLSource source, boolean isDeclaration)
			throws UnsatisfiablePathConditionException {
		TypeEvaluation typeEval = getDynamicType(state, pid, type, source,
				isDeclaration);
		SymbolicExpression expr = symbolicUtil.expressionOfType(type,
				typeEval.type);
		Evaluation result = new Evaluation(typeEval.state, expr);

		return result;
	}

	/**
	 * Evaluates an abstract function call.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the expression belongs to.
	 * @param expression
	 *            The abstract function call expression to be evaluated.
	 * @return The value of the expression and the new state.
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateAbstractFunctionCall(State state, int pid,
			AbstractFunctionCallExpression expression)
			throws UnsatisfiablePathConditionException {
		AbstractFunction function = expression.function();
		SymbolicType returnType = function.returnType()
				.getDynamicType(universe);
		List<SymbolicType> argumentTypes = new ArrayList<SymbolicType>();
		List<SymbolicExpression> arguments = new ArrayList<SymbolicExpression>();
		SymbolicType functionType;
		SymbolicExpression functionExpression;
		SymbolicExpression functionApplication;
		Evaluation result;
		String functionName = function.name().name();

		for (Variable param : function.parameters()) {
			argumentTypes.add(param.type().getDynamicType(universe));
		}
		for (Expression arg : expression.arguments()) {
			Evaluation eval = evaluate(state, pid, arg);
			arguments.add(eval.value);
		}
		functionType = universe.functionType(argumentTypes, returnType);
		if (functionName.startsWith("$"))
			functionName = ABSTRACT_FUNCTION_PREFIX + functionName;
		functionExpression = universe.symbolicConstant(
				universe.stringObject(functionName), functionType);
		functionApplication = universe.apply(functionExpression, arguments);
		result = new Evaluation(state, functionApplication);
		return result;
	}

	/**
	 * Evaluates an address-of expression <code>&e</code>.
	 * 
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            PID of the process performing the evaluation
	 * @param expression
	 *            the address-of expression
	 * @return the symbolic expression of pointer type resulting from evaluating
	 *         the address of the argument and a new state (if there is
	 *         side-effect, otherwise just return the original state)
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateAddressOf(State state, int pid,
			AddressOfExpression expression)
			throws UnsatisfiablePathConditionException {
		if (expression.isFieldOffset()) {
			CIVLType structType = expression.getTypeForOffset();
			SymbolicExpression typeValue = this.symbolicUtil.expressionOfType(
					structType, structType.getDynamicType(universe));
			SymbolicExpression value = universe.apply(offsetFunction,
					Arrays.asList(typeValue,
							universe.integer(expression.getFieldIndex())));
			return new Evaluation(state, value);
		} else
			return reference(state, pid, expression.operand());
	}

	/**
	 * Evaluates a short-circuit "and" expression <code>p && q</code>.
	 * 
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            PID of the process evaluating this expression
	 * @param expression
	 *            the and expression
	 * @return the result of applying the AND operator to the two arguments
	 *         together with the post-state whose path condition may contain the
	 *         side-effects resulting from evaluation
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateAnd(State state, int pid,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.left());
		BooleanExpression leftValue = (BooleanExpression) eval.value;
		BooleanExpression assumption = eval.state.getPathCondition(universe);
		Reasoner reasoner = universe.reasoner(assumption);

		// true && x = x;
		// TODO is it more efficient to call canonic before the valid call?
		if (reasoner.isValid(leftValue))
			return evaluate(eval.state, pid, expression.right());
		if (reasoner.isValid(universe.not(leftValue))) {
			// false && x = false;
			eval.value = universe.falseExpression();
			return eval;
		} else {
			eval = evaluate(eval.state, pid, expression.right());
			eval.value = universe.and(leftValue,
					(BooleanExpression) eval.value);
			// eval.state = tmp;
			return eval;
		}
	}

	/**
	 * Evaluates an array literal expression, like
	 * <code>{[1] = a, [2] = 3, [6]=9}</code>;
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The array literal expression.
	 * @return The symbolic representation of the array literal expression and
	 *         the new state if there is side effect.
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateArrayLiteral(State state, int pid,
			ArrayLiteralExpression expression)
			throws UnsatisfiablePathConditionException {
		Expression[] elements = expression.elements();
		SymbolicType symbolicElementType;
		List<SymbolicExpression> symbolicElements = new ArrayList<>();
		Evaluation eval;

		for (Expression element : elements) {
			eval = evaluate(state, pid, element);
			symbolicElements.add(eval.value);
			state = eval.state;
		}
		// The symbolic element type is get from the function "getDynamicType()"
		// which won't give any information about extents, so we have to add it
		// if it's complete array type.
		if (expression.elementType() instanceof CIVLCompleteArrayType) {
			Pair<State, SymbolicType> pair;

			pair = getCompleteArrayType(state, pid,
					((CIVLCompleteArrayType) expression.elementType()));
			state = pair.left;
			symbolicElementType = pair.right;
		} else
			symbolicElementType = expression.elementType()
					.getDynamicType(universe);
		return new Evaluation(state,
				universe.array(symbolicElementType, symbolicElements));
	}

	private Pair<State, SymbolicType> getCompleteArrayType(State state, int pid,
			CIVLCompleteArrayType elementType)
			throws UnsatisfiablePathConditionException {
		SymbolicType arrayType;
		Evaluation eval;
		Pair<State, SymbolicType> pair;

		if (elementType.elementType() instanceof CIVLCompleteArrayType) {
			pair = this.getCompleteArrayType(state, pid,
					(CIVLCompleteArrayType) elementType.elementType());
			state = pair.left;
			arrayType = pair.right;
		} else
			arrayType = elementType.elementType().getDynamicType(universe);
		eval = this.evaluate(state, pid, elementType.extent());
		state = eval.state;
		assert eval.value instanceof NumericExpression;
		return new Pair<State, SymbolicType>(state,
				universe.arrayType(arrayType, (NumericExpression) eval.value));
	}

	/**
	 * Evaluates a binary expression. Either this throws an unsatisfiable path
	 * condition exception or it returns a non-null state and a non-null value
	 * if there is no error during the evaluation.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The PID of the currently executing process.
	 * @param process
	 *            The name of the process for error report.
	 * @param expression
	 *            The binary expression.
	 * @return A symbolic expression for the binary operation and a new state if
	 *         there is side-effect.
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateBinary(State state, int pid, String process,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		BINARY_OPERATOR operator = expression.operator();

		switch (operator) {
			case AND :
				return evaluateAnd(state, pid, expression);
			case OR :
				return evaluateOr(state, pid, expression);
			// TODO code review
			case IMPLIES :
				return evaluateImplies(state, pid, expression);
			case BIT_AND :
				return evaluateBitand(state, pid, expression);
			case BIT_OR :
				return evaluateBitor(state, pid, expression);
			case BIT_XOR :
				return evaluateBitxor(state, pid, expression);
			case SHIFTLEFT :
				return evaluateShiftleft(state, pid, expression);
			case SHIFTRIGHT :
				return evaluateShiftright(state, pid, expression);
			case DIVIDE :
			case LESS_THAN :
			case LESS_THAN_EQUAL :
			case MINUS :
			case MODULO :
			case PLUS :
			case POINTER_ADD :
			case POINTER_SUBTRACT :
			case TIMES :
				// numeric expression like +,-,*,/,%,etc
				if (expression.left().getExpressionType() != null
						&& expression.left().getExpressionType()
								.equals(typeFactory.scopeType())) {
					return evaluateScopeOperations(state, pid, expression);
				} else {
					return evaluateNumericOperations(state, pid, process,
							expression);
				}
			case NOT_EQUAL :
			case EQUAL :
				return evaluateNumericOperations(state, pid, process,
						expression);
			case REMOTE :
			default :
				throw new CIVLUnimplementedFeatureException(
						"Evaluating binary operator of " + operator + " kind");
		}
	}

	/**
	 * Evaluates a bit and expression.
	 * 
	 * @param state
	 *            The state where the evaluation happens.
	 * @param pid
	 *            The PID of the process that triggers the evaluation.
	 * @param expression
	 *            The bit and expression to be evaluated.
	 * @return A possibly new state resulted from side effects during the
	 *         evaluation and the value of the bit and expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateBitand(State state, int pid,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.left());
		SymbolicExpression left = eval.value, right, result;

		eval = evaluate(eval.state, pid, expression.right());
		right = eval.value;
		state = eval.state;
		result = universe.bitand((NumericExpression) left,
				(NumericExpression) right);
		return new Evaluation(state, result);
	}

	/**
	 * Evaluates a bit complement expression.
	 * 
	 * @param state
	 *            The state where the evaluation happens.
	 * @param pid
	 *            The PID of the process that triggers the evaluation.
	 * @param expression
	 *            The bit complement expression to be evaluated.
	 * @return A possibly new state resulted from side effects during the
	 *         evaluation and the value of the bit complement expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateBitcomplement(State state, int pid,
			UnaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.operand());
		SymbolicExpression operand = eval.value, result;

		state = eval.state;
		result = universe.bitnot((NumericExpression) operand);
		return new Evaluation(state, result);
	}

	/**
	 * Evaluates a bit or expression.
	 * 
	 * @param state
	 *            The state where the evaluation happens.
	 * @param pid
	 *            The PID of the process that triggers the evaluation.
	 * @param expression
	 *            The bit or expression to be evaluated.
	 * @return A possibly new state resulted from side effects during the
	 *         evaluation and the value of the bit or expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateBitor(State state, int pid,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.left());
		SymbolicExpression left = eval.value, right, result;

		eval = evaluate(eval.state, pid, expression.right());
		right = eval.value;
		state = eval.state;
		result = universe.bitor((NumericExpression) left,
				(NumericExpression) right);
		return new Evaluation(state, result);
	}

	/**
	 * Evaluates a bit xor expression.
	 * 
	 * @param state
	 *            The state where the evaluation happens.
	 * @param pid
	 *            The PID of the process that triggers the evaluation.
	 * @param expression
	 *            The bit xor expression to be evaluated.
	 * @return A possibly new state resulted from side effects during the
	 *         evaluation and the value of the bit xor expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateBitxor(State state, int pid,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.left());
		SymbolicExpression left = eval.value, right, result;

		eval = evaluate(eval.state, pid, expression.right());
		right = eval.value;
		state = eval.state;
		result = universe.bitxor((NumericExpression) left,
				(NumericExpression) right);
		return new Evaluation(state, result);
	}

	/**
	 * Evaluate a boolean literal expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The boolean literal expression.
	 * @return The symbolic representation of the boolean literal expression and
	 *         the new state if there is side effect during the evaluation.
	 */
	protected Evaluation evaluateBooleanLiteral(State state, int pid,
			BooleanLiteralExpression expression) {
		return new Evaluation(state, universe.bool(expression.value()));
	}

	/**
	 * Evaluates a cast expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param process
	 *            The process name for error report.
	 * @param expression
	 *            The cast expression.
	 * @return A possibly new state resulted from side effects during the
	 *         evaluation and the value of the cast expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateCast(State state, int pid, String process,
			CastExpression expression)
			throws UnsatisfiablePathConditionException {
		return this.evaluateCastWorker(state, pid, process,
				expression.getCastType(), expression.getExpression());
	}

	@Override
	public Evaluation evaluateCastWorker(State state, int pid, String process,
			CIVLType castType, Expression arg)
			throws UnsatisfiablePathConditionException {
		CIVLType argType = arg.getExpressionType();
		Evaluation eval = evaluate(state, pid, arg);
		SymbolicExpression value = eval.value;
		TypeEvaluation typeEval = getDynamicType(eval.state, pid, castType,
				arg.getSource(), false);
		SymbolicType endType = typeEval.type;

		state = typeEval.state;
		if (argType.isDomainType() && castType.isDomainType()) {
			return new Evaluation(state, value);
		} else if (argType.isBoolType() && castType.isIntegerType()) {
			eval.value = this.booleanToInteger(value);
			return eval;
		} else if (argType.isIntegerType() && castType.isPointerType()) {
			eval.value = this.int2PointerCaster
					.apply(state.getPathCondition(universe), value, castType);
			return eval;
		} else if (argType.isPointerType() && castType.isIntegerType()) {
			eval.value = this.pointer2IntCaster
					.apply(state.getPathCondition(universe), value, null);
			return eval;
		} else if (argType.isPointerType() && castType.isPointerType()) {
			// pointer to pointer: for now...no change.
			CIVLType argBaseType = ((CIVLPointerType) argType).baseType(),
					castBaseType = ((CIVLPointerType) castType).baseType();

			if (castBaseType.isFunction()) {
				return eval;
			} else if (!castBaseType.isCharType() && !argBaseType.isCharType()
					&& !castBaseType.isVoidType() && !argBaseType.isVoidType()
					&& !argBaseType.equals(castBaseType)) {
				// eval.value.type()
				throw new CIVLUnimplementedFeatureException(
						"type conversion from pointer-to-" + argBaseType
								+ " to pointer-to-" + castBaseType,
						arg.getSource());
			}
			return eval;
		} else if (argType.isIntegerType() && castType.isBoolType()) {
			if (value.type().isBoolean())
				eval.value = value;
			else
				eval.value = universe.not(universe.equals(value, zero));
			return eval;
		} else if (argType.isIntegerType() && castType.isCharType()) {
			eval.value = this.int2CharCaster
					.apply(state.getPathCondition(universe), value, null);
			return eval;
		} else if (argType.isCharType() && castType.isIntegerType()) {
			eval.value = this.char2IntCaster
					.apply(state.getPathCondition(universe), value, null);
			return eval;
		}
		try {
			eval.value = universe.cast(endType, eval.value);
		} catch (SARLException e) {
			errorLogger.logSimpleError(arg.getSource(), state, process,
					this.symbolicAnalyzer.stateInformation(state),
					ErrorKind.INVALID_CAST, "SARL could not cast: " + e);
			throw new UnsatisfiablePathConditionException();
		}
		return eval;
	}

	/**
	 * Evaluates a char literal expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The char literal expression.
	 * @return A possibly new state resulted from side effects during the
	 *         evaluation and the value of the char literal expression.
	 */
	protected Evaluation evaluateCharLiteral(State state, int pid,
			CharLiteralExpression expression) {
		return new Evaluation(state, universe.character(expression.value()));
	}

	/**
	 * Evaluates a dereference expression <code>*e</code>.
	 * 
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            PID of the process performing the evaluation
	 * @param process
	 *            The process name for error report.
	 * @param expression
	 *            the dereference expression
	 * @return the evaluation with the properly updated state and the value
	 *         after the dereference.
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateDereference(State state, int pid,
			String process, DereferenceExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.pointer());
		CIVLType referredType = expression.getExpressionType();

		return dereference(expression.pointer().getSource(), eval.state,
				process, referredType, eval.value, true, true);
	}

	/**
	 * Evaluates a derivative call expression.
	 * 
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            the PID of the process running this call
	 * @param expression
	 *            the derivative call expression to be evaluated
	 * @return the evaluation with the properly updated state and the value of
	 *         the derivative call expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateDerivativeCall(State state, int pid,
			DerivativeCallExpression expression)
			throws UnsatisfiablePathConditionException {
		AbstractFunction function = expression.function();
		SymbolicType returnType = function.returnType()
				.getDynamicType(universe);
		List<SymbolicType> argumentTypes = new ArrayList<SymbolicType>();
		List<SymbolicExpression> arguments = new ArrayList<SymbolicExpression>();
		SymbolicType functionType;
		SymbolicExpression functionExpression;
		SymbolicExpression functionApplication;
		Evaluation result;
		String derivativeName;

		for (Variable param : function.parameters()) {
			argumentTypes.add(param.type().getDynamicType(universe));
		}
		for (Expression arg : expression.arguments()) {
			Evaluation eval = evaluate(state, pid, arg);
			arguments.add(eval.value);
		}
		functionType = universe.functionType(argumentTypes, returnType);
		// The derivative name is the name of the function concatenated with the
		// names and degrees of the partials. e.g. the name of
		// $D[rho,{x,1},{y,2}]() is "rhox1y2"
		derivativeName = function.name().name();
		for (Pair<Variable, IntegerLiteralExpression> partial : expression
				.partials()) {
			derivativeName += partial.left.name().name()
					+ partial.right.value();
		}
		functionExpression = universe.symbolicConstant(
				universe.stringObject(derivativeName), functionType);
		functionApplication = universe.apply(functionExpression, arguments);
		result = new Evaluation(state, functionApplication);
		return result;
	}

	/**
	 * Evaluates a domain guard expression, the value of which is true iff there
	 * is a subsequent element of of the current one in the domain object. See
	 * also {@link DomainGuardExpression}.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param domainGuard
	 *            The domain guard expression to be evaluated, which contains
	 *            the information of the current domain element and the domain
	 *            object.
	 * @return the evaluation with the properly updated state and the value of
	 *         the domain guard expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateDomainGuard(State state, int pid,
			DomainGuardExpression domainGuard)
			throws UnsatisfiablePathConditionException {
		Expression domain = domainGuard.domain();
		int dimension = domainGuard.dimension();
		// Collection for storing given domain element.
		List<SymbolicExpression> domElement = new LinkedList<>();
		SymbolicExpression domainValue;
		// The value of the domain union.
		SymbolicExpression domainUnion;
		Evaluation eval = this.evaluate(state, pid, domain);
		// Result, if there is a subsequence.
		boolean hasNext = false;
		// Flag indicating the given domain element only contains NULLs.
		boolean isAllNull = true;

		state = eval.state;
		domainValue = eval.value;
		domainUnion = universe.tupleRead(domainValue, twoObj);
		// Evaluating the value of the given element.
		for (int i = 0; i < dimension; i++) {
			SymbolicExpression varValue = state.valueOf(pid,
					domainGuard.variableAt(i));

			domElement.add(varValue);
			if (!varValue.isNull())
				isAllNull = false;
		}
		// If the domain object is a rectangular domain
		if (symbolicUtil.isRectangularDomain(domainValue)) {
			SymbolicExpression recDom = universe.unionExtract(zeroObj,
					domainUnion);

			if (isAllNull)
				hasNext = !symbolicUtil.isEmptyDomain(domainValue, dimension,
						domain.getSource());
			else
				hasNext = symbolicUtil.recDomainHasNext(recDom, dimension,
						domElement);
			eval.state = state;
			// TODO:rectangular domain always has concrete ranges so that the
			// result is always concrete ?
			eval.value = universe.bool(hasNext);
		} else if (symbolicUtil.isLiteralDomain(domainValue)) {
			Variable literalDomCounterVar;

			// TODO: is there a domain that contains none elements ?
			if (isAllNull)
				hasNext = !symbolicUtil.isEmptyDomain(domainValue, dimension,
						domain.getSource());
			else {
				NumericExpression literalCounter;
				NumericExpression domainSize = symbolicUtil
						.getDomainSize(domainValue);
				int counter, size;

				// Compare the literal domain counter and the size of the
				// domain.
				literalDomCounterVar = domainGuard.getLiteralDomCounter();
				literalCounter = (NumericExpression) state.valueOf(pid,
						literalDomCounterVar);
				counter = ((IntegerNumber) universe
						.extractNumber(literalCounter)).intValue();
				size = ((IntegerNumber) universe.extractNumber(domainSize))
						.intValue();
				hasNext = counter < size;
			}
		} else
			throw new CIVLInternalException(
					"A domain object is neither a rectangular domain nor a literal domain",
					domainGuard.getSource());
		eval.state = state;
		eval.value = universe.bool(hasNext);
		return eval;
	}

	/**
	 * Evaluates the value of a rectangular domain literal expression.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param recDomain
	 *            The expression of the rectangular domain
	 * @return The evaluation with the properly updated state and the value of
	 *         the rectangular domain literal expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateRecDomainLiteral(State state, int pid,
			RecDomainLiteralExpression recDomain)
			throws UnsatisfiablePathConditionException {
		int dim = recDomain.dimension();
		List<SymbolicExpression> ranges = new ArrayList<>();
		Evaluation eval;
		SymbolicExpression domainV;
		SymbolicType domainType;
		// For a rectangular domain, its range types are all the same.
		// because rectangular domain is an array of ranges
		SymbolicType rangeType;
		List<SymbolicExpression> domValueComponents = new LinkedList<>();
		// ranges should be in form of an array inside a domain.
		SymbolicExpression rangesArray;
		CIVLDomainType civlDomType;
		CIVLType civlRangeType;

		for (int i = 0; i < dim; i++) {
			eval = evaluate(state, pid, recDomain.rangeAt(i));
			state = eval.state;
			ranges.add(eval.value);
		}
		rangeType = ranges.get(0).type();
		civlRangeType = typeFactory.rangeType();
		civlDomType = typeFactory.domainType(civlRangeType);
		domainType = civlDomType.getDynamicType(universe);
		assert domainType instanceof SymbolicTupleType : "Dynamic $domain type is not a tuple type";
		assert rangeType instanceof SymbolicTupleType : "Dynamic $range type is not a tuple type";
		// Adding components
		domValueComponents.add(universe.integer(dim));
		// Union field index which indicates it's a rectangular domain.
		domValueComponents.add(zero);
		rangesArray = universe.array(rangeType, ranges);
		domValueComponents.add(universe.unionInject(
				civlDomType.getDynamicSubTypesUnion(universe), zeroObj,
				rangesArray));
		// The cast is guaranteed
		// TODO: when is the appropriate time to call universe.canonic() ?
		domainV = universe.canonic(universe
				.tuple((SymbolicTupleType) domainType, domValueComponents));
		return new Evaluation(state, domainV);
	}

	/**
	 * Evaluates a "dot" expression used to navigate to a field in a record,
	 * <code>e.f</code>.
	 * 
	 * @param state
	 *            The state of the model
	 * @param pid
	 *            The PID of the process evaluating this expression
	 * @param expression
	 *            The dot expression to evaluated
	 * @return The evaluation which contains the result of evaluating the
	 *         expression together with the post-state which may incorporate
	 *         side-effects resulting from the evaluation
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateDot(State state, int pid, String process,
			DotExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.structOrUnion());
		SymbolicExpression structValue = eval.value;
		int fieldIndex = expression.fieldIndex();

		if (expression.isStruct()) {
			eval.value = universe.tupleRead(structValue,
					universe.intObject(fieldIndex));
		} else {
			BooleanExpression test = universe
					.unionTest(universe.intObject(fieldIndex), structValue);

			if (test.isFalse()) {
				errorLogger.logSimpleError(expression.getSource(), eval.state,
						process, this.symbolicAnalyzer.stateInformation(state),
						ErrorKind.UNION,
						"Attempt to access an invalid union member");
				throw new UnsatisfiablePathConditionException();
			}
			eval.value = universe.unionExtract(universe.intObject(fieldIndex),
					structValue);
		}
		return eval;
	}

	/**
	 * Evaluates a dynamic type of expression. TODO what's this for?
	 * 
	 * @param state
	 * @param pid
	 * @param expression
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateDynamicTypeOf(State state, int pid,
			DynamicTypeOfExpression expression)
			throws UnsatisfiablePathConditionException {
		return dynamicTypeOf(state, pid, expression.getType(),
				expression.getSource(), true);
	}

	/**
	 * Evaluates a function guard expression. When the function is a system
	 * function, the evaluation inquires the corresponding library for its
	 * evaluation; otherwise, the result is always the true value.
	 * 
	 * @param state
	 * @param pid
	 * @param process
	 * @param expression
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateFunctionGuard(State state, int pid,
			String process, FunctionGuardExpression expression)
			throws UnsatisfiablePathConditionException {
		Triple<State, CIVLFunction, Integer> eval = this
				.evaluateFunctionIdentifier(state, pid,
						expression.functionExpression(),
						expression.getSource());
		CIVLFunction function;

		state = eval.first;
		function = eval.second;
		if (function == null) {
			errorLogger.logSimpleError(expression.getSource(), state, process,
					symbolicAnalyzer.stateInformation(state), ErrorKind.OTHER,
					"function body cann't be found");
			throw new UnsatisfiablePathConditionException();
		}
		if (function.isSystemFunction()) {
			SystemFunction systemFunction = (SystemFunction) function;

			return this.evaluateGuardofSystemFunction(expression.getSource(),
					state, pid, systemFunction.getLibrary(), systemFunction,
					expression.arguments());
		}
		return new Evaluation(state, universe.trueExpression());
	}

	protected Evaluation evaluateFunctionIdentifierExpression(State state,
			int pid, FunctionIdentifierExpression expression) {
		Scope scope = expression.scope();
		SymbolicExpression dyScopeId = modelFactory
				.scopeValue(state.getDyscope(pid, scope));
		SymbolicExpression functionPointer = universe
				.tuple(this.functionPointerType, Arrays.asList(dyScopeId,
						universe.integer(expression.function().fid())));

		return new Evaluation(state, functionPointer);
	}

	protected Evaluation evaluateHereOrRootScope(State state, int pid,
			HereOrRootExpression expression) {
		int dyScopeID = expression.isRoot()
				? state.rootDyscopeID()
				: state.getProcessState(pid).getDyscopeId();

		return new Evaluation(state, modelFactory.scopeValue(dyScopeID));
	}

	/**
	 * Evaluates a short-circuit "implies" expression "p=?q".
	 * 
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            PID of the process evaluating this expression
	 * @param expression
	 *            the and expression
	 * @return the result of applying the IMPLIES operator to the two arguments
	 *         together with the post-state whose path condition may contain the
	 *         side-effects resulting from evaluation
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateImplies(State state, int pid,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.left());
		BooleanExpression p = (BooleanExpression) eval.value;
		BooleanExpression assumption = eval.state.getPathCondition(universe);
		Reasoner reasoner = universe.reasoner(assumption);

		// If p is false, the implication will evaluate to true.
		if (reasoner.isValid(universe.not(p))) {
			eval.value = universe.trueExpression();
			return eval;
		} else {
			eval = evaluate(eval.state, pid, expression.right());
			eval.value = universe.implies(p, (BooleanExpression) eval.value);
			return eval;
		}
	}

	/**
	 * <p>
	 * <b><Summary: </b>
	 * 
	 * Evaluates an {@link InitialValueExpression}. An
	 * {@link InitialValueExpression} is an initial value that will be assigned
	 * to an uninitialized variable.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the current process
	 * @param expression
	 *            The {@link InitialValueExpression} that will be evaluated
	 * @return The {@link Evaluation} of the {@link InitialValueExpression}
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateInitialValue(State state, int pid,
			InitialValueExpression expression)
			throws UnsatisfiablePathConditionException {
		Variable variable = expression.variable();
		CIVLType type = variable.type();

		if (type.isArrayType())
			if (((CIVLArrayType) type).isComplete())
				state = checkArrayExtentDeclaration(state, pid,
						(CIVLCompleteArrayType) type, expression.getSource());

		TypeEvaluation typeEval = getDynamicType(state, pid, type,
				expression.getSource(), false);
		int sid = typeEval.state.getDyscopeID(pid, variable);

		return computeInitialValue(typeEval.state, pid, variable, typeEval.type,
				sid);
	}

	/**
	 * <p>
	 * <b>Summary: </b> Checks of a given complete array type T satisfies such
	 * property: <code>
	 * array_extent_predicate(T) := 
	 *            extent(T) > 0 && 
	 *            elementTypeOf(T) is an complete array type ==> 
	 *                          array_extent_predicate(elementTypeOf(T))
	 *                          </code>
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the current process
	 * @param arrayType
	 *            The given {@link CIVLCompleteArrayType} that will be checked
	 * @param source
	 *            The {@link CIVLSource} related to this checking. It will be
	 *            used to report when the check fails.
	 * @return A new state after checking
	 * @throws UnsatisfiablePathConditionException
	 */
	private State checkArrayExtentDeclaration(State state, int pid,
			CIVLCompleteArrayType arrayType, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		Expression extent = arrayType.extent();
		Evaluation eval = evaluate(state, pid, extent);
		BooleanExpression validArrayLength;
		Reasoner reasoner = universe.reasoner(state.getPathCondition(universe));
		ResultType resultType;

		state = eval.state;
		validArrayLength = universe.lessThan(zero,
				(NumericExpression) eval.value);
		resultType = reasoner.valid(validArrayLength).getResultType();
		if (resultType != ResultType.YES) {
			state = errorLogger.logError(source, state, pid,
					symbolicAnalyzer.stateInformation(state), validArrayLength,
					resultType, ErrorKind.ARRAY_DECLARATION,
					"Array extent must be greater thean zero.");
		}
		if (arrayType.elementType().isArrayType()) {
			CIVLArrayType elementType = (CIVLArrayType) arrayType.elementType();

			if (elementType.isComplete())
				return checkArrayExtentDeclaration(state, pid,
						(CIVLCompleteArrayType) elementType, source);
		}
		return state;
	}

	/**
	 * Computes the symbolic initial value of a variable.
	 * 
	 * @param state
	 *            The state where the computation happens.
	 * @param pid
	 *            The PID of the process that triggers the computation.
	 * @param variable
	 *            The variable to be evaluated.
	 * @param dynamicType
	 *            The symbolic type of the variable.
	 * @param dyscopeId
	 *            The dynamic scope ID of the current state.
	 * @return The symbolic initial value of the given variable
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation computeInitialValue(State state, int pid,
			Variable variable, SymbolicType dynamicType, int dyscopeId)
			throws UnsatisfiablePathConditionException {
		CIVLType type = variable.type();
		SymbolicExpression result;

		if (!variable.isInput() && variable.isStatic()) {
			return initialValueOfType(state, pid, type);
		} else if (!variable.isInput() && !variable.isBound()
				&& (type instanceof CIVLPrimitiveType || type.isPointerType()
						|| type.isDomainType())) {
			result = nullExpression;
		} else {// the case of an input variable or a variable of
			// array/struct/union type.
			String name;
			StringObject nameObj;

			// TODO temporarily doing this for contract verification, ultimately
			// this should be fixed and the scope id checking should be an
			// assertion instead
			if (variable.isInput() && variable.scope()
					.id() == ModelConfiguration.STATIC_ROOT_SCOPE) {
				// if (variable.isInput()){
				// assert (variable.scope().id() ==
				// ModelConfiguration.STATIC_ROOT_SCOPE);
				name = "X_" + variable.name().name();
				nameObj = universe.stringObject(name);

				result = universe.symbolicConstant(nameObj, dynamicType);
			} else {
				Pair<State, SymbolicConstant> freshSymbol = this.stateFactory
						.getFreshSymbol(state,
								ModelConfiguration.HAVOC_PREFIX_INDEX,
								dynamicType);

				state = freshSymbol.left;
				result = freshSymbol.right;
			}
		}
		return new Evaluation(state, result);
	}

	/**
	 * Evaluates an integer literal expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The integer literal expression.
	 * @return The symbolic representation of the integer literal expression.
	 */
	protected Evaluation evaluateIntegerLiteral(State state, int pid,
			IntegerLiteralExpression expression) {
		return new Evaluation(state,
				universe.integer(expression.value().intValue()));
	}

	protected Evaluation evaluateNumericOperations(State state, int pid,
			String process, BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = this.evaluate(state, pid, expression.left());
		SymbolicExpression left = eval.value;
		SymbolicExpression right;

		eval = evaluate(eval.state, pid, expression.right());
		right = eval.value;
		switch (expression.operator()) {
			case PLUS :
				eval.value = universe.add((NumericExpression) left,
						(NumericExpression) right);
				break;
			case MINUS :
				eval.value = universe.subtract((NumericExpression) left,
						(NumericExpression) right);
				break;
			case TIMES :
				eval.value = universe.multiply((NumericExpression) left,
						(NumericExpression) right);
				break;
			case DIVIDE :
				return evaluateDivide(eval.state, pid, expression,
						(NumericExpression) left, (NumericExpression) right);
			case LESS_THAN :
				eval.value = universe.lessThan((NumericExpression) left,
						(NumericExpression) right);
				break;
			case LESS_THAN_EQUAL :
				eval.value = universe.lessThanEquals((NumericExpression) left,
						(NumericExpression) right);
				break;
			// equal and not_equal operators support scope, process, and pointer
			// types. If the value of those types is undefined (e.g., process
			// -1,
			// scope -1, pointer<-1, ..., ...>), an error should be reported.
			case EQUAL : {
				SymbolicType leftType = left.type(), rightType = right.type();

				// if (!this.civlConfig.svcomp()) {
				this.isValueDefined(eval.state, process, expression.left(),
						left);
				this.isValueDefined(eval.state, process, expression.right(),
						right);
				// }
				if (leftType.isBoolean() && rightType.isInteger()) {
					left = booleanToInteger(left);
				} else if (leftType.isInteger() && rightType.isBoolean()) {
					right = booleanToInteger(right);
				}
				eval.value = universe.equals(left, right);
				break;
			}
			case NOT_EQUAL : {
				SymbolicType leftType = left.type(), rightType = right.type();

				this.isValueDefined(eval.state, process, expression.left(),
						left);
				this.isValueDefined(eval.state, process, expression.right(),
						right);
				if (leftType.isBoolean() && rightType.isInteger()) {
					left = booleanToInteger(left);
				} else if (leftType.isInteger() && rightType.isBoolean()) {
					right = booleanToInteger(right);
				}
				eval.value = universe.neq(left, right);
				break;
			}
			case MODULO :
				eval = evaluateModulo(eval.state, pid, expression,
						(NumericExpression) left, (NumericExpression) right);
				break;
			case POINTER_ADD :
				eval = evaluatePointerAdd(eval.state, pid, process, expression,
						left, (NumericExpression) right);
				break;
			case POINTER_SUBTRACT : {
				if (right.isNumeric())
					eval = this.evaluatePointerAdd(state, pid, process,
							expression, left,
							universe.minus((NumericExpression) right));
				else
					eval = pointerSubtraction(eval.state, pid, process,
							expression, left, right);
				break;

			}
			case IMPLIES :
			case AND :
			case OR :
				throw new CIVLInternalException("unreachable", expression);
			default :
				throw new CIVLUnimplementedFeatureException(
						"Evaluating numeric operator " + expression.operator(),
						expression);
		}
		return eval;
	}

	/**
	 * <p>
	 * Evaluates a modulo operation.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the calling process
	 * @param expression
	 *            A {@link BinaryExpression} which represents a division
	 *            operation.
	 * @param numerator
	 *            The value of the numerator
	 * @param denominator
	 *            The value of the denominator
	 * @return The evaluation of this operation.
	 * @throws UnsatisfiablePathConditionException
	 *             When the denominator equals to zero.
	 */
	protected Evaluation evaluateModulo(State state, int pid,
			BinaryExpression expression, NumericExpression numerator,
			NumericExpression denominator)
			throws UnsatisfiablePathConditionException {
		return evaluateModuloWorker(state, pid, expression, numerator,
				denominator, false);
	}

	/**
	 * <p>
	 * Worker method for evaluating a modulo operation.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the calling process
	 * @param expression
	 *            A {@link BinaryExpression} which represents a division
	 *            operation.
	 * @param numerator
	 *            The value of the numerator
	 * @param denominator
	 *            The value of the denominator
	 * @param muteErrorSideEffects
	 *            Division by zero error will NOT be reported iff this parameter
	 *            is set to true.
	 * @return The evaluation of this operation.
	 * @throws UnsatisfiablePathConditionException
	 *             When the denominator equals to zero.
	 */
	protected Evaluation evaluateModuloWorker(State state, int pid,
			BinaryExpression expression, NumericExpression numerator,
			NumericExpression denominator, boolean muteErrorSideEffects)
			throws UnsatisfiablePathConditionException {
		BooleanExpression assumption = state.getPathCondition(universe);

		if (civlConfig.svcomp() || muteErrorSideEffects) {
			BooleanExpression leftPositive = universe.lessThan(zero, numerator);
			ResultType resultType = universe.reasoner(assumption)
					.valid(leftPositive).getResultType();

			if (resultType != ResultType.YES) {
				numerator = universe.add(
						universe.modulo(numerator, denominator), denominator);
			}
		} else {
			BooleanExpression claim = universe
					.neq(zeroOf(expression.getSource(),
							expression.getExpressionType()), denominator);
			ResultType resultType = universe.reasoner(assumption).valid(claim)
					.getResultType();

			if (resultType != ResultType.YES)
				state = errorLogger.logError(expression.getSource(), state, pid,
						symbolicAnalyzer.stateInformation(state), claim,
						resultType, ErrorKind.DIVISION_BY_ZERO,
						"Modulus denominator is zero");
		}
		return new Evaluation(state, universe.modulo(numerator, denominator));
	}

	/**
	 * <p>
	 * Evaluates a division operation.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the calling process
	 * @param expression
	 *            A {@link BinaryExpression} which represents a division
	 *            operation.
	 * @param numerator
	 *            The value of the numerator
	 * @param denominator
	 *            The value of the denominator
	 * @return The evaluation of this operation.
	 * @throws UnsatisfiablePathConditionException
	 *             When the denominator equals to zero.
	 */
	protected Evaluation evaluateDivide(State state, int pid,
			BinaryExpression expression, NumericExpression numerator,
			NumericExpression denominator)
			throws UnsatisfiablePathConditionException {
		return this.evaluateDivideWorker(state, pid, expression, numerator,
				denominator, false);
	}

	/**
	 * <p>
	 * Worker method for evaluating a division operation.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the calling process
	 * @param expression
	 *            A {@link BinaryExpression} which represents a division
	 *            operation.
	 * @param numerator
	 *            The value of the numerator
	 * @param denominator
	 *            The value of the denominator
	 * @param muteErrorSideEffects
	 *            Division by zero error will NOT be reported iff this parameter
	 *            is set to true
	 * @return The evaluation of this operation.
	 * @throws UnsatisfiablePathConditionException
	 *             When the denominator equals to zero.
	 */
	protected Evaluation evaluateDivideWorker(State state, int pid,
			BinaryExpression expression, NumericExpression numerator,
			NumericExpression denominator, boolean muteErrorSideEffects)
			throws UnsatisfiablePathConditionException {
		BooleanExpression assumption = state.getPathCondition(universe);
		SymbolicExpression result;

		if (civlConfig.checkDivisionByZero() && !muteErrorSideEffects
				&& !expression.getExpressionType().isIntegerType()) {
			SymbolicExpression zero = zeroOf(expression.getSource(),
					expression.getExpressionType());
			BooleanExpression claim = universe.neq(zero, denominator);
			ResultType resultType = universe.reasoner(assumption).valid(claim)
					.getResultType();

			if (resultType != ResultType.YES) {
				Expression divisor = expression.right();

				state = errorLogger.logError(expression.getSource(), state, pid,
						this.symbolicAnalyzer.stateInformation(state), claim,
						resultType, ErrorKind.DIVISION_BY_ZERO,
						"division by zero where divisor: " + expression.right()
								+ "="
								+ this.symbolicAnalyzer
										.symbolicExpressionToString(
												divisor.getSource(), state,
												divisor.getExpressionType(),
												denominator));
			}
		}
		result = universe.divide((NumericExpression) numerator, denominator);
		return new Evaluation(state, result);
	}

	private SymbolicExpression booleanToInteger(
			SymbolicExpression booleanValue) {
		if (booleanValue.isTrue())
			return one;
		else if (booleanValue.isFalse())
			return zero;
		else
			return this.universe.cond((BooleanExpression) booleanValue, one,
					zero);
	}

	/**
	 * Evaluates a short-circuit "or" expression "p||q".
	 * 
	 * @param state
	 *            the pre-state
	 * @param pid
	 *            PID of the process evaluating this expression
	 * @param expression
	 *            the OR expression
	 * @return the result of applying the OR operator to the two arguments
	 *         together with the post-state whose path condition may contain the
	 *         side-effects resulting from evaluation
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateOr(State state, int pid,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.left());
		BooleanExpression p = (BooleanExpression) eval.value;
		BooleanExpression assumption = eval.state.getPathCondition(universe);
		Reasoner reasoner = universe.reasoner(assumption);

		// TODO: handle special common case as in evaluateAnd.
		// Look at evaluation of ternary operator too?
		if (reasoner.isValid(p)) {
			eval.value = universe.trueExpression();
			return eval;
		}
		if (reasoner.isValid(universe.not(p))) {
			return evaluate(eval.state, pid, expression.right());
		} else {
			eval = evaluate(eval.state, pid, expression.right());
			eval.value = universe.or(p, (BooleanExpression) eval.value);
			return eval;
		}
	}

	protected SymbolicExpression lambda(State state, int pid,
			NumericSymbolicConstant[] boundVariables, int boundIndex,
			SymbolicFunctionType arrayType, Expression body)
			throws UnsatisfiablePathConditionException {
		NumericSymbolicConstant index = boundVariables[boundIndex];
		SymbolicExpression eleValue;
		Evaluation eval;

		if (boundIndex == boundVariables.length - 1) {
			eval = this.evaluate(state, pid, body);
			eleValue = eval.value;
			state = eval.state;
		} else {
			eleValue = lambda(state, pid, boundVariables, boundIndex + 1,
					arrayType, body);
		}
		return universe.lambda(index, eleValue);
	}

	/**
	 * Creates an array lambda symbolic expression recursively (If it is a
	 * multi-dimensional array, the created one will be a nested array lambda
	 * expression).
	 * 
	 * 
	 * @param state
	 *            The state where the array lambda expression body will evaluate
	 * @param pid
	 *            The PID of the process who invokes the creation of array
	 *            lambda expressions.
	 * @param boundVariables
	 *            An array of bound variables specified by the array lambda
	 *            expression
	 * @param boundIndex
	 *            The index of the bound variable in the array which belongs to
	 *            the current sub-array-lambda expression.
	 * @param arrayType
	 *            The symbolic type of a array lambda expression, which must be
	 *            a complete array type
	 * @param body
	 *            The lambda expression body of the array lambda
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	protected SymbolicExpression arrayLambda(State state, int pid,
			NumericSymbolicConstant[] boundVariables, int boundIndex,
			SymbolicCompleteArrayType arrayType, Expression body)
			throws UnsatisfiablePathConditionException {
		NumericSymbolicConstant index = boundVariables[boundIndex];
		SymbolicExpression eleValue;
		SymbolicExpression arrayEleFunction;
		Evaluation eval;
		BooleanExpression arrayIndexingConstraint = universe.and(
				universe.lessThanEquals(this.zero, index),
				universe.lessThan(index, arrayType.extent()));

		state = stateFactory.addToPathcondition(state, pid,
				arrayIndexingConstraint);
		if (boundIndex == boundVariables.length - 1) {
			eval = this.evaluate(state, pid, body);
			eleValue = eval.value;
			state = eval.state;
		} else {
			eleValue = arrayLambda(state, pid, boundVariables, boundIndex + 1,
					(SymbolicCompleteArrayType) arrayType.elementType(), body);
		}
		arrayEleFunction = universe.lambda(index, eleValue);
		return universe.arrayLambda(arrayType, arrayEleFunction);
	}

	//
	// // TODO break into small functions
	// protected Evaluation evaluateQuantifiedExpression(State state, int pid,
	// QuantifiedExpression expression)
	// throws UnsatisfiablePathConditionException {
	// Evaluation result;
	// Evaluation quantifiedExpression;
	// BooleanExpression context;
	// Reasoner reasoner;
	// BooleanExpression simplifiedExpression;
	// SymbolicConstant boundVariable = universe.symbolicConstant(expression
	// .boundVariableName().stringObject(), expression
	// .boundVariableType().getDynamicType(universe));
	// State stateWithRestriction;
	//
	// boundVariables.push(boundVariable);
	// if (expression.isRange()) {
	// Evaluation range = evaluate(state, pid, expression.restriction());
	// // Evaluation lower = evaluate(state, pid, expression.lower());
	// // Evaluation upper = evaluate(state, pid, expression.upper());
	// BooleanExpression rangeRestriction;
	// NumericExpression lower, upper, upperBound;
	// ResultType isRestrictionInValid;
	//
	// assert expression.restriction().getExpressionType()
	// .equals(this.typeFactory.rangeType());
	// lower = this.symbolicUtil.getLowOfRegularRange(range.value);
	// upper = this.symbolicUtil.getHighOfRegularRange(range.value);
	// if (!this.symbolicUtil.getStepOfRegularRange(range.value).isOne()) {
	// errorLogger
	// .logSimpleError(
	// expression.getSource(),
	// state,
	// state.getProcessState(pid).name(),
	// this.symbolicAnalyzer.stateInformation(state),
	// ErrorKind.OTHER,
	// "the range expression of bound variables in "
	// + "quantified expression only allows one as the step");
	// throw new UnsatisfiablePathConditionException();
	// }
	// // assert lower.value instanceof NumericExpression;
	// // assert upper.value instanceof NumericExpression;
	// upperBound = universe.add(one, upper);
	// rangeRestriction = universe.and(universe.lessThanEquals(lower,
	// (NumericExpression) boundVariable), universe
	// .lessThanEquals((NumericExpression) boundVariable, upper));
	// reasoner = universe.reasoner(state.getPathCondition());
	// isRestrictionInValid = reasoner.valid(
	// universe.not(rangeRestriction)).getResultType();
	// if (isRestrictionInValid == ResultType.YES) {
	// // invalid range restriction
	// switch (expression.quantifier()) {
	// case EXISTS:
	// result = new Evaluation(state, universe.falseExpression());
	// break;
	// default:// FORALL UNIFORM
	// result = new Evaluation(state, universe.trueExpression());
	// }
	// } else {
	// // TODO change to andTo
	// stateWithRestriction = state.setPathCondition(universe.and(
	// (BooleanExpression) rangeRestriction,
	// state.getPathCondition()));
	// quantifiedExpression = evaluate(stateWithRestriction, pid,
	// expression.expression());
	// switch (expression.quantifier()) {
	// case EXISTS:
	// result = new Evaluation(state, universe.existsInt(
	// (NumericSymbolicConstant) boundVariable, lower,
	// upperBound,
	// (BooleanExpression) quantifiedExpression.value));
	// break;
	// case FORALL:
	// result = new Evaluation(state, universe.forallInt(
	// (NumericSymbolicConstant) boundVariable, lower,
	// upperBound,
	// (BooleanExpression) quantifiedExpression.value));
	// break;
	// case UNIFORM:
	// result = new Evaluation(state, universe.forallInt(
	// (NumericSymbolicConstant) boundVariable, lower,
	// upperBound,
	// (BooleanExpression) quantifiedExpression.value));
	// break;
	// default:
	// throw new CIVLException("Unknown quantifier ",
	// expression.getSource());
	// }
	// }
	// } else {
	// Evaluation restriction = evaluate(state, pid,
	// expression.restriction());
	// Interval interval = null;
	// NumericExpression lower = null, upper = null;
	// ResultType isRestrictionInValid;
	//
	// reasoner = universe.reasoner(state.getPathCondition());
	// isRestrictionInValid = reasoner.valid(
	// universe.not((BooleanExpression) restriction.value))
	// .getResultType();
	// if (isRestrictionInValid == ResultType.YES) {
	// // invalid range restriction
	// switch (expression.quantifier()) {
	// case EXISTS:
	// result = new Evaluation(state, universe.falseExpression());
	// break;
	// default:// FORALL UNIFORM
	// result = new Evaluation(state, universe.trueExpression());
	// }
	// } else {
	// stateWithRestriction = state.setPathCondition(universe.and(
	// (BooleanExpression) restriction.value,
	// state.getPathCondition()));
	// quantifiedExpression = evaluate(stateWithRestriction, pid,
	// expression.expression());
	// // By definition, the restriction should be boolean valued.
	// assert restriction.value instanceof BooleanExpression;
	// context = universe.and(state.getPathCondition(),
	// (BooleanExpression) restriction.value);
	// reasoner = universe.reasoner(context);
	// simplifiedExpression = (BooleanExpression) reasoner
	// .simplify(quantifiedExpression.value);
	// interval = reasoner.assumptionAsInterval(boundVariable);
	// if (interval != null) {
	// lower = universe.number(interval.lower());
	// upper = universe.add(universe.number(interval.upper()),
	// this.one);
	// }
	// switch (expression.quantifier()) {
	// case EXISTS:
	// if (interval != null)
	// result = new Evaluation(
	// state,
	// universe.existsInt(
	// (NumericSymbolicConstant) boundVariable,
	// lower,
	// upper,
	// (BooleanExpression) simplifiedExpression));
	// else
	// result = new Evaluation(state, universe.exists(
	// boundVariable, universe.and(
	// (BooleanExpression) restriction.value,
	// simplifiedExpression)));
	// break;
	// case FORALL:
	// if (interval != null)
	// result = new Evaluation(
	// state,
	// universe.forallInt(
	// (NumericSymbolicConstant) boundVariable,
	// lower,
	// upper,
	// (BooleanExpression) simplifiedExpression));
	// else
	// result = new Evaluation(state, universe.forall(
	// boundVariable, universe.implies(
	// (BooleanExpression) restriction.value,
	// simplifiedExpression)));
	// break;
	// case UNIFORM:
	// if (interval != null)
	// result = new Evaluation(
	// state,
	// universe.forallInt(
	// (NumericSymbolicConstant) boundVariable,
	// lower,
	// upper,
	// (BooleanExpression) simplifiedExpression));
	// else
	// result = new Evaluation(state, universe.forall(
	// boundVariable, universe.implies(
	// (BooleanExpression) restriction.value,
	// simplifiedExpression)));
	// break;
	// default:
	// throw new CIVLException("Unknown quantifier ",
	// expression.getSource());
	// }
	// }
	//
	// }
	// boundVariables.pop();
	// return result;
	// }

	protected Evaluation evaluateRegularRange(State state, int pid,
			RegularRangeExpression range)
			throws UnsatisfiablePathConditionException {
		SymbolicTupleType type = (SymbolicTupleType) range.getExpressionType()
				.getDynamicType(universe);
		Evaluation eval = this.evaluate(state, pid, range.getLow());
		SymbolicExpression low, high, step, rangeValue;
		BooleanExpression claim;
		boolean negativeStep = false;
		ResultType validity;
		String process = state.getProcessState(pid).name() + "(id = " + pid
				+ ")";

		low = eval.value;
		state = eval.state;
		eval = evaluate(state, pid, range.getHigh());
		high = eval.value;
		state = eval.state;
		eval = evaluate(state, pid, range.getStep());
		step = eval.value;
		state = eval.state;
		claim = universe.equals(this.zero, step);
		validity = universe.reasoner(state.getPathCondition(universe))
				.valid(claim).getResultType();
		if (validity == ResultType.YES) {
			errorLogger.logSimpleError(range.getSource(), state, process,
					symbolicAnalyzer.stateInformation(state), ErrorKind.OTHER,
					"a regular range expression requires a non-zero step");
			throw new UnsatisfiablePathConditionException();
		}
		claim = universe.lessThan(this.zero, (NumericExpression) step);
		validity = universe.reasoner(state.getPathCondition(universe))
				.valid(claim).getResultType();
		if (validity == ResultType.NO)
			negativeStep = true;
		if (negativeStep) {
			SymbolicExpression tmp = low;

			low = high;
			high = tmp;
		}
		rangeValue = universe.tuple(type, Arrays.asList(low, high, step));
		return new Evaluation(state, rangeValue);
	}

	protected Evaluation evaluateScopeOperations(State state, int pid,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.left());
		int left = modelFactory.getScopeId(eval.value);
		int right;
		boolean result;

		state = eval.state;
		eval = evaluate(state, pid, expression.right());
		state = eval.state;
		right = modelFactory.getScopeId(eval.value);
		switch (expression.operator()) {
			case PLUS :
				int lowestCommonAncestor = stateFactory
						.lowestCommonAncestor(state, left, right);

				eval.value = modelFactory.scopeValue(lowestCommonAncestor);
				break;
			case LESS_THAN :
				result = stateFactory.isDescendantOf(state, right, left);
				eval.value = universe.bool(result);
				break;
			case LESS_THAN_EQUAL :
				result = (left == right)
						? true
						: stateFactory.isDescendantOf(state, right, left);
				eval.value = universe.bool(result);
				break;
			case EQUAL :
				eval.value = universe.bool(left == right);
				break;
			case NOT_EQUAL :
				eval.value = universe.bool(left != right);
				break;
			default :
				throw new CIVLUnimplementedFeatureException(
						"evaluting scope operator " + expression.operator(),
						expression.getSource());
		}
		return eval;
	}

	protected Evaluation evaluateSizeofExpressionExpression(State state,
			int pid, SizeofExpression expression)
			throws UnsatisfiablePathConditionException {
		return evaluateSizeofType(expression.getSource(), state, pid,
				expression.getArgument().getExpressionType());
	}

	protected Evaluation evaluateSizeofTypeExpression(State state, int pid,
			SizeofTypeExpression expression)
			throws UnsatisfiablePathConditionException {
		return evaluateSizeofType(expression.getSource(), state, pid,
				expression.getTypeArgument());
	}

	/**
	 * <p>
	 * Evaluating a subscript expression.
	 * </p>
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The array index expression.
	 * @return A symbolic expression for an array read.
	 */
	protected Evaluation evaluateSubscript(State state, int pid, String process,
			SubscriptExpression expression)
			throws UnsatisfiablePathConditionException {
		return this.evaluateSubscriptWorker(state, pid, process, expression,
				false);
	}

	/**
	 * <p>
	 * Worker method for evaluating a subscript expression.
	 * </p>
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The array index expression.
	 * @param muteErrorSideEffect
	 *            Array index out-of bound error will NOT be reported iff this
	 *            parameter sets to true.
	 * @return A symbolic expression for an array read.
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateSubscriptWorker(State state, int pid,
			String process, SubscriptExpression expression,
			boolean muteErrorSideEffect)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.array());
		SymbolicExpression array = eval.value;
		SymbolicArrayType arrayType = (SymbolicArrayType) array.type();
		NumericExpression index;

		eval = evaluate(state, pid, expression.index());
		index = (NumericExpression) eval.value;
		if (!muteErrorSideEffect)
			eval.state = checkArrayIndexInBound(eval.state, pid,
					expression.getSource(), arrayType, array, index, false);
		eval.value = universe.arrayRead(array, index);
		return eval;
	}

	private State checkArrayIndexInBound(State state, int pid,
			CIVLSource source, SymbolicArrayType arrayType,
			SymbolicExpression array, NumericExpression index,
			boolean addressOnly) throws UnsatisfiablePathConditionException {
		if (!this.civlConfig.svcomp() && arrayType.isComplete()) {
			NumericExpression length = universe.length(array);
			BooleanExpression assumption = state.getPathCondition(universe);
			// TODO change to andTo
			BooleanExpression claim;
			ResultType resultType;
			Reasoner reasoner = universe.reasoner(assumption);

			claim = universe.lessThanEquals(zero, index);
			resultType = reasoner.valid(claim).getResultType();
			if (resultType != ResultType.YES) {
				state = errorLogger.logError(source, state, pid,
						symbolicAnalyzer.stateInformation(state), claim,
						resultType, ErrorKind.OUT_OF_BOUNDS,
						"possible negative array index: " + index);
			}
			if (addressOnly)
				claim = universe.lessThanEquals(index, length);
			else
				claim = universe.lessThan(index, length);
			resultType = reasoner.valid(claim).getResultType();
			if (resultType != ResultType.YES) {
				state = errorLogger.logError(source, state, pid,
						symbolicAnalyzer.stateInformation(state), claim,
						resultType, ErrorKind.OUT_OF_BOUNDS,
						"out of bounds array index:\nindex = " + index
								+ "\nlength = " + length);
			}
		}
		return state;
	}

	protected Evaluation evaluateSelf(State state, int pid,
			SelfExpression expression) {
		return new Evaluation(state, stateFactory.processValue(pid));
	}

	protected Evaluation evaluateProcnull(State state, int pid,
			ProcnullExpression expression) {
		return new Evaluation(state, modelFactory.nullProcessValue());
	}

	/**
	 * Evaluate a real literal expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The real literal expression.
	 * @return The symbolic representation of the real literal expression.
	 */
	protected Evaluation evaluateRealLiteral(State state, int pid,
			RealLiteralExpression expression) {
		return new Evaluation(state, universe.number(universe.numberObject(
				numberFactory.rational(expression.value().toPlainString()))));
	}

	protected Evaluation evaluateScopeofExpression(State state, int pid,
			String process, ScopeofExpression expression)
			throws UnsatisfiablePathConditionException {
		LHSExpression argument = expression.argument();

		return evaluateScopeofExpressionWorker(state, pid, process, argument);
	}

	private Evaluation evaluateScopeofExpressionWorker(State state, int pid,
			String process, LHSExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval;

		switch (expression.lhsExpressionKind()) {
			case DEREFERENCE :
				Expression pointer = ((DereferenceExpression) expression)
						.pointer();

				eval = evaluate(state, pid, pointer);
				int sid = symbolicUtil.getDyscopeId(pointer.getSource(),
						eval.value);
				state = eval.state;
				if (sid < 0) {
					errorLogger.logSimpleError(pointer.getSource(), state,
							process, symbolicAnalyzer.stateInformation(state),
							ErrorKind.DEREFERENCE,
							"Attempt to dereference pointer into scope which has been removed from state");
					throw new UnsatisfiablePathConditionException();
				}
				return new Evaluation(state, modelFactory.scopeValue(sid));
			case DOT :
				return evaluateScopeofExpressionWorker(state, pid, process,
						(LHSExpression) (((DotExpression) expression)
								.structOrUnion()));
			case SUBSCRIPT :
				return evaluateScopeofExpressionWorker(state, pid, process,
						(LHSExpression) (((SubscriptExpression) expression)
								.array()));

			case VARIABLE :// VARIABLE
				int scopeId = state.getDyscopeID(pid,
						((VariableExpression) expression).variable());

				return new Evaluation(state, modelFactory.scopeValue(scopeId));
			default :
				throw new CIVLUnimplementedFeatureException(
						"scope of expression with operand of "
								+ expression.lhsExpressionKind() + " kind");
		}
	}

	protected Evaluation evaluateShiftleft(State state, int pid,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.left());
		SymbolicExpression left = eval.value, right, result;

		eval = evaluate(eval.state, pid, expression.right());
		right = eval.value;
		state = eval.state;
		if (left instanceof BooleanPrimitive)
			left = left.isTrue() ? universe.integer(1) : universe.integer(0);
		result = universe.bitshiftLeft((NumericExpression) left,
				(NumericExpression) right);
		return new Evaluation(state, result);
	}

	protected Evaluation evaluateShiftright(State state, int pid,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.left());
		SymbolicExpression left = eval.value, right, result;

		eval = evaluate(eval.state, pid, expression.right());
		right = eval.value;
		state = eval.state;
		if (left instanceof BooleanPrimitive)
			left = left.isTrue() ? universe.integer(1) : universe.integer(0);
		result = universe.bitshiftRight((NumericExpression) left,
				(NumericExpression) right);
		return new Evaluation(state, result);
	}

	/**
	 * Evaluate a struct literal expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The struct literal expression.
	 * @return The symbolic representation of the struct literal expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateStructOrUnionLiteral(State state, int pid,
			StructOrUnionLiteralExpression expression)
			throws UnsatisfiablePathConditionException {
		Expression[] fields = expression.fields();
		SymbolicType dynamicStructType = expression.getExpressionType()
				.getDynamicType(universe);
		ArrayList<SymbolicExpression> symbolicFields = new ArrayList<>();
		Evaluation eval;

		if (expression.isStruct()) {
			for (Expression field : fields) {
				eval = evaluate(state, pid, field);
				symbolicFields.add(eval.value);
				state = eval.state;
			}
			assert dynamicStructType instanceof SymbolicTupleType;
			return new Evaluation(state, universe.tuple(
					(SymbolicTupleType) dynamicStructType, symbolicFields));
		} else {
			int numberOfMembers = fields.length;
			SymbolicExpression unionValue;
			SymbolicUnionType unionType = (SymbolicUnionType) dynamicStructType;

			assert dynamicStructType instanceof SymbolicUnionType;
			eval = evaluate(state, pid, fields[numberOfMembers - 1]);
			state = eval.state;
			unionValue = universe.unionInject(unionType,
					universe.intObject(numberOfMembers - 1), eval.value);

			return new Evaluation(state, unionValue);
		}
	}

	/**
	 * Evaluate a unary expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The unary expression.
	 * @return The symbolic representation of the unary expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateUnary(State state, int pid,
			UnaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.operand());

		switch (expression.operator()) {
			case NEGATIVE :
				eval.value = universe.minus((NumericExpression) eval.value);
				break;
			case NOT :
				eval.value = universe.not((BooleanExpression) eval.value);
				break;
			case BIG_O :
				eval.value = universe.apply(bigOFunction,
						new Singleton<SymbolicExpression>(eval.value));
				break;
			case BIT_NOT :
				return evaluateBitcomplement(state, pid, expression);
			default :
				throw new CIVLUnimplementedFeatureException(
						"evaluating unary operator " + expression.operator(),
						expression);
		}
		return eval;
	}

	/**
	 * Evaluate a variable expression.
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The pid of the currently executing process.
	 * @param expression
	 *            The variable expression.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateVariable(State state, int pid, String process,
			VariableExpression expression, boolean checkUndefinedValue)
			throws UnsatisfiablePathConditionException {
		if (expression.variable().isOutput()) {
			errorLogger.logSimpleError(expression.getSource(), state, process,
					this.symbolicAnalyzer.stateInformation(state),
					ErrorKind.OUTPUT_READ,
					"attempt to read the output variable "
							+ expression.variable().name());
			throw new UnsatisfiablePathConditionException();
		} else {
			SymbolicExpression value = state.valueOf(pid,
					expression.variable());

			if (checkUndefinedValue && value.isNull()) {
				errorLogger.logSimpleError(expression.getSource(), state,
						process, this.symbolicAnalyzer.stateInformation(state),
						ErrorKind.UNDEFINED_VALUE,
						"attempt to read uninitialized variable " + expression);
				throw new UnsatisfiablePathConditionException();
			}
			return new Evaluation(state, value);
		}
	}

	/**
	 * evaluate a the guard of a system function at a certain state with a list
	 * of arguments
	 * 
	 * @param source
	 *            the source information for error report
	 * @param state
	 *            The state where the computation happens.
	 * @param pid
	 *            The ID of the process that wants to evaluate the guard.
	 * @param library
	 *            the library that the system function belongs to
	 * @param function
	 *            the system function
	 * @param arguments
	 *            the list of arguments
	 * @return The result of the evaluation, including the state and the
	 *         symbolic expression of the value.
	 * @throws UnsatisfiablePathConditionException
	 *             if there is no contract specifying the guard and the library
	 *             evaluator is missing
	 */
	protected Evaluation evaluateGuardofSystemFunction(CIVLSource source,
			State state, int pid, String library, CIVLFunction function,
			List<Expression> arguments)
			throws UnsatisfiablePathConditionException {
		if (function.functionContract() != null) {
			Expression guard = function.functionContract().guard();

			if (guard != null) {
				if (guard.constantValue() != null)
					return new Evaluation(state, guard.constantValue());

				int numArgs = arguments.size();
				SymbolicExpression[] argumentValues = new SymbolicExpression[numArgs];
				Evaluation eval;

				for (int i = 0; i < numArgs; i++) {
					Expression arg = arguments.get(i);

					eval = this.evaluate(state, pid, arg);
					state = eval.state;
					argumentValues[i] = eval.value;
				}
				state = stateFactory.pushCallStack(state, pid, function,
						argumentValues);
				return this.evaluate(state, pid, guard);
			}
		}
		return getSystemGuard(source, state, pid, library,
				function.name().name(), arguments);
	}

	@Override
	public TypeEvaluation getDynamicType(State state, int pid, CIVLType type,
			CIVLSource source, boolean isDefinition)
			throws UnsatisfiablePathConditionException {
		TypeEvaluation result;

		// if type has a state variable and computeStructs is false, use
		// variable else compute
		if (type instanceof CIVLPrimitiveType) {
			result = new TypeEvaluation(state, type.getDynamicType(universe));
		} else if (type instanceof CIVLPointerType) {
			result = new TypeEvaluation(state, pointerType);
		} else if (type.getStateVariable() != null && !isDefinition) {
			SymbolicExpression value = state.valueOf(pid,
					type.getStateVariable());

			result = new TypeEvaluation(state,
					symbolicUtil.getType(source, value));
		} else if (type instanceof CIVLArrayType) {
			CIVLArrayType arrayType = (CIVLArrayType) type;
			TypeEvaluation elementTypeEval = getDynamicType(state, pid,
					arrayType.elementType(), source, false);

			if (arrayType.isComplete()) {
				Evaluation lengthEval = evaluate(elementTypeEval.state, pid,
						((CIVLCompleteArrayType) arrayType).extent());
				NumericExpression length = (NumericExpression) lengthEval.value;

				result = new TypeEvaluation(lengthEval.state,
						universe.arrayType(elementTypeEval.type, length));
			} else {
				result = new TypeEvaluation(elementTypeEval.state,
						universe.arrayType(elementTypeEval.type));
			}
		} else if (type instanceof CIVLStructOrUnionType) {
			CIVLStructOrUnionType structType = (CIVLStructOrUnionType) type;
			int numFields = structType.numFields();
			LinkedList<SymbolicType> componentTypes = new LinkedList<SymbolicType>();
			SymbolicType symbolicType;

			for (int i = 0; i < numFields; i++) {
				StructOrUnionField field = structType.getField(i);
				TypeEvaluation componentEval = getDynamicType(state, pid,
						field.type(), source, false);

				state = componentEval.state;
				componentTypes.add(componentEval.type);
			}
			if (structType.isStructType())
				symbolicType = universe.tupleType(
						structType.name().stringObject(), componentTypes);
			else
				symbolicType = universe.unionType(
						structType.name().stringObject(), componentTypes);
			result = new TypeEvaluation(state, symbolicType);
		} else if (type instanceof CIVLBundleType) {
			result = new TypeEvaluation(state, type.getDynamicType(universe));
		} else if (type instanceof CIVLHeapType) {
			result = new TypeEvaluation(state, this.heapType);
		} else if (type instanceof CIVLEnumType) {
			result = new TypeEvaluation(state, type.getDynamicType(universe));
		} else if (type instanceof CIVLDomainType) {
			result = new TypeEvaluation(state, type.getDynamicType(universe));
		} else if (type instanceof CIVLFunctionType) {
			result = new TypeEvaluation(state, type.getDynamicType(universe));
		} else
			throw new CIVLInternalException("Unreachable", source);
		return result;
	}

	protected Evaluation getSystemGuard(CIVLSource source, State state, int pid,
			String library, String function, List<Expression> arguments)
			throws UnsatisfiablePathConditionException {
		try {
			LibraryEvaluator libEvaluator = this.libLoader.getLibraryEvaluator(
					library, this, this.modelFactory, symbolicUtil,
					symbolicAnalyzer);
			Expression[] args = new Expression[arguments.size()];

			arguments.toArray(args);
			return libEvaluator.evaluateGuard(source, state, pid, function,
					args);
		} catch (LibraryLoaderException exception) {
			String process = state.getProcessState(pid).name() + "(id=" + pid
					+ ")";
			StringBuffer message = new StringBuffer();
			int numArgs = arguments.size();
			SymbolicExpression[] argumentValues = new SymbolicExpression[numArgs];

			for (int i = 0; i < numArgs; i++) {
				Evaluation eval = this.evaluate(state, pid, arguments.get(i));

				state = eval.state;
				argumentValues[i] = eval.value;
			}
			message.append(
					"unable to load the library evaluator for the library ");
			message.append(library);
			message.append(" for the function ");
			message.append(function);
			this.errorLogger.logSimpleError(source, state, process,
					this.symbolicAnalyzer.stateInformation(state),
					ErrorKind.LIBRARY, message.toString());
			return new Evaluation(state,
					this.symbolicUtil.getAbstractGuardOfFunctionCall(library,
							function, argumentValues));
		}
	}

	// private Set<SymbolicExpression> heapCells(State state, int dyscopeId) {
	// SymbolicExpression heapValue = state.getVariableValue(dyscopeId, 0);
	//
	// if (heapValue.isNull())
	// return new HashSet<>();
	// else {
	// CIVLHeapType heapType = modelFactory.heapType();
	// int numMallocs = heapType.getNumMallocs();
	// Set<SymbolicExpression> result = new HashSet<>();
	//
	// for (int i = 0; i < numMallocs; i++) {
	// ReferenceExpression ref = universe.tupleComponentReference(
	// identityReference, universe.intObject(i));
	// SymbolicExpression heapCell = symbolicUtil.makePointer(
	// dyscopeId, 0, ref);
	//
	// result.add(heapCell);
	// }
	// return result;
	// }
	// }

	// TODO: add doc here
	private Evaluation initialValueOfType(State state, int pid, CIVLType type)
			throws UnsatisfiablePathConditionException {
		TypeKind kind = type.typeKind();
		Evaluation eval = null;

		switch (kind) {
			case ARRAY : {
				CIVLArrayType arrayType = (CIVLArrayType) type;
				CIVLType elementType = arrayType.elementType();

				eval = new Evaluation(state, universe
						.emptyArray(elementType.getDynamicType(universe)));
				break;
			}
			case COMPLETE_ARRAY : {
				CIVLCompleteArrayType arrayType = (CIVLCompleteArrayType) type;
				CIVLType elementType = arrayType.elementType();
				SymbolicExpression elementValue;
				NumericExpression extent;
				TypeEvaluation teval;

				eval = initialValueOfType(state, pid, elementType);
				state = eval.state;
				elementValue = eval.value;
				eval = this.evaluate(state, pid, arrayType.extent());
				state = eval.state;
				extent = (NumericExpression) eval.value;
				// using "evaluator.getDynamicType" so that extent info won't be
				// lost:
				teval = getDynamicType(state, pid, elementType, null, false);
				state = teval.state;
				eval.value = symbolicUtil.newArray(
						state.getPathCondition(universe), teval.type, extent,
						elementValue);
				break;
			}
			case BUNDLE :
				eval = new Evaluation(state, universe.nullExpression());
				break;
			case DOMAIN : {
				CIVLDomainType domainType = (CIVLDomainType) type;
				SymbolicExpression initDomainValue;
				int dim;
				SymbolicType integerType = universe.integerType();
				SymbolicTupleType tupleType = universe.tupleType(
						universe.stringObject("domain"),
						Arrays.asList(integerType, integerType, universe
								.arrayType(universe.arrayType(integerType))));
				List<SymbolicExpression> tupleComponents = new LinkedList<>();

				tupleComponents.add(one);
				tupleComponents.add(one);
				tupleComponents.add(
						universe.emptyArray(universe.arrayType(integerType)));
				if (domainType.isComplete()) {
					CIVLCompleteDomainType compDomainType = (CIVLCompleteDomainType) domainType;

					dim = compDomainType.getDimension();
					tupleComponents.set(0, universe.integer(dim));

				}
				initDomainValue = universe.tuple(tupleType, tupleComponents);
				eval = new Evaluation(state, initDomainValue);
				break;
			}
			case ENUM : {
				CIVLEnumType enumType = (CIVLEnumType) type;

				eval = new Evaluation(state,
						universe.integer(enumType.firstValue()));
				break;
			}
			case POINTER :
				eval = new Evaluation(state, symbolicUtil.nullPointer());
				break;
			case PRIMITIVE : {
				CIVLPrimitiveType primitiveType = (CIVLPrimitiveType) type;

				eval = new Evaluation(state,
						primitiveType.initialValue(universe));
				break;
			}
			default :// STRUCT_OR_UNION{ // TODO: don't make this the default!
			{
				CIVLStructOrUnionType strOrUnion = (CIVLStructOrUnionType) type;

				if (strOrUnion.isUnionType()) {
					eval = this.initialValueOfType(state, pid,
							strOrUnion.getField(0).type());
					eval.value = universe.unionInject(
							(SymbolicUnionType) strOrUnion
									.getDynamicType(universe),
							this.zeroObj, eval.value);
				} else {
					int size = strOrUnion.numFields();
					List<SymbolicExpression> components = new ArrayList<>(size);

					for (int i = 0; i < size; i++) {
						eval = this.initialValueOfType(state, pid,
								strOrUnion.getField(i).type());
						state = eval.state;
						components.add(eval.value);
					}
					eval = new Evaluation(state,
							universe.tuple(
									(SymbolicTupleType) strOrUnion
											.getDynamicType(universe),
									components));
				}
			}
		}
		return eval;
	}

	/**
	 * Checks if a value of type scope, process, or pointer type is defined. If
	 * the value of those types is undefined (e.g., process -1, scope -1,
	 * pointer<-1, ..., ...>), an error should be reported.
	 * 
	 * @param state
	 *            The state where the checking happens.
	 * @param expression
	 *            The static representation of the value.
	 * @param expressionValue
	 *            The symbolic value to be checked if it is defined.
	 * @throws UnsatisfiablePathConditionException
	 */
	private void isValueDefined(State state, String process,
			Expression expression, SymbolicExpression expressionValue)
			throws UnsatisfiablePathConditionException {
		CIVLSource source = expression.getSource();
		CIVLType expressionType = expression.getExpressionType();

		if (expressionType.equals(typeFactory.scopeType())) {
			if (expressionValue.equals(modelFactory
					.undefinedValue(typeFactory.scopeSymbolicType()))) {
				errorLogger.logSimpleError(source, state, process,
						symbolicAnalyzer.stateInformation(state),
						ErrorKind.UNDEFINED_VALUE,
						"Attempt to evaluate an invalid scope reference");
				throw new UnsatisfiablePathConditionException();
			}
		} else if (expressionType.equals(typeFactory.processType())) {
			if (expressionValue.equals(modelFactory
					.undefinedValue(typeFactory.processSymbolicType()))) {
				errorLogger.logSimpleError(source, state, process,
						symbolicAnalyzer.stateInformation(state),
						ErrorKind.UNDEFINED_VALUE,
						"Attempt to evaluate an invalid process reference");
				throw new UnsatisfiablePathConditionException();
			}
		} else if (expressionValue.type().equals(this.pointerType)) {
			if (this.civlConfig.svcomp()) {
				if (expressionValue.operator() != SymbolicOperator.TUPLE)
					return;
			}
			if (this.symbolicUtil.isNullPointer(expressionValue))
				return;
			if (this.symbolicUtil.applyReverseFunction(INT_TO_POINTER_FUNCTION,
					expressionValue) != null)
				return;
			if (expressionValue.operator() != SymbolicOperator.TUPLE)
				return;
			// try {
			int scopeID = symbolicUtil.getDyscopeId(source, expressionValue);

			if (scopeID < 0) {
				StringBuffer message = new StringBuffer();

				message.append(
						"Attempt to evaluate a pointer refererring to memory of an invalid scope:\n");
				message.append(
						"pointer expression: " + expression.toString() + "\n");
				message.append("value: " + expressionValue);
				errorLogger.logSimpleError(source, state, process,
						symbolicAnalyzer.stateInformation(state),
						ErrorKind.MEMORY_LEAK, message.toString());
				throw new UnsatisfiablePathConditionException();
			}
			// } catch (Exception e) {
			// errorLogger.logSimpleError(source, state, process,
			// symbolicAnalyzer.stateInformation(state),
			// ErrorKind.UNDEFINED_VALUE,
			// "Attempt to use undefined pointer");
			// throw new UnsatisfiablePathConditionException();
			// }
		}
	}

	/**
	 * zero
	 * 
	 * @param source
	 * @param type
	 * @return
	 */
	protected NumericExpression zeroOf(CIVLSource source, CIVLType type) {
		if (type instanceof CIVLPrimitiveType) {
			if (((CIVLPrimitiveType) type)
					.primitiveTypeKind() == PrimitiveTypeKind.INT)
				return zero;
			if (((CIVLPrimitiveType) type)
					.primitiveTypeKind() == PrimitiveTypeKind.REAL)
				return zeroR;
		}
		throw new CIVLInternalException(
				"Expected integer or real type, not " + type, source);
	}

	/*
	 * ********************* Pointer addition helpers ************************
	 */
	/**
	 * <p>
	 * This is a helper function for
	 * {@link Evaluator#evaluatePointerAdd(State, int, String, BinaryExpression, SymbolicExpression, NumericExpression)}
	 * . <br>
	 * 
	 * For the given pointer who has an {@link ArrayElementReference}, this
	 * method performs the pointer addition operation by adding the given offset
	 * to the ArrayElementReference and possibly other
	 * ancestor-ArrayElementReferences.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The String identifier of the process
	 * @param pointer
	 *            The {@link SymbolicExpression} of the original pointer before
	 *            addition
	 * @param offset
	 *            The {@link NumericExpression} of the offset will be added on
	 *            the pointer
	 * @param checkOutput
	 *            Dereferencing operation has to check if the object pointed by
	 *            input pointer is an output variable if this flag is set TRUE
	 * @param muteErrorSideEffects
	 *            This method will NOT report error side-effects iff this
	 *            parameter set to true.
	 * @param source
	 *            {@link CIVLSource} of the pointer addition statement
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 * 
	 * @author ziqing
	 */
	protected Pair<Evaluation, NumericExpression[]> arrayElementReferenceAddWorker(
			State state, int pid, SymbolicExpression pointer,
			NumericExpression offset, boolean muteErrorSideEffects,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression arrayPtr;
		NumericExpression extent, index;
		BooleanExpression zeroOffset, inBound;
		Evaluation eval;
		int scopeId = symbolicUtil.getDyscopeId(source, pointer);
		int vid = symbolicUtil.getVariableId(source, pointer);
		Reasoner reasoner = universe.reasoner(state.getPathCondition(universe));
		ReferenceExpression ref = symbolicUtil.getSymRef(pointer);
		String process = state.getProcessState(pid).name();

		zeroOffset = universe.equals(offset, zero);
		if (offset.isZero() || reasoner.isValid(zeroOffset))
			return new Pair<>(new Evaluation(state, pointer), null);
		assert ref.isArrayElementReference();
		arrayPtr = symbolicUtil.parentPointer(pointer);
		index = ((ArrayElementReference) ref).getIndex();

		SymbolicType dyType = symbolicAnalyzer.dynamicTypeOfObjByPointer(source,
				state, arrayPtr);
		SymbolicArrayType dyArrayType;
		ReferenceExpression newRef;

		assert dyType != null && dyType.typeKind() == SymbolicTypeKind.ARRAY;
		dyArrayType = (SymbolicArrayType) dyType;
		if (dyArrayType.isComplete()) {
			NumericExpression totalOffset = universe.add(index, offset);
			ResultType resultType = null;

			extent = ((SymbolicCompleteArrayType) dyArrayType).extent();
			// In bound condition: greater than or equal to the lower bound &&
			// lower than the upper bound:
			inBound = universe.and(universe.lessThanEquals(zero, totalOffset),
					universe.lessThan(totalOffset, extent));
			// Conditions of recomputing array indices:
			// If the parent pointer points to an element of an array object as
			// well and it can be proved that the result of the pointer addition
			// will point to other sub-arrays.
			if (!symbolicUtil.isPointer2MemoryBlock(arrayPtr) && symbolicUtil
					.getSymRef(arrayPtr).isArrayElementReference()) {
				resultType = reasoner.valid(inBound).getResultType();
				if (resultType == ResultType.NO)
					return recomputeArrayIndices(state, pid, vid, scopeId,
							pointer, offset, reasoner, muteErrorSideEffects,
							source);
				else if (resultType != ResultType.YES) {
					SymbolicExpression newPtr0, newPtr1;
					Pair<Evaluation, NumericExpression[]> result = recomputeArrayIndices(
							state, pid, vid, scopeId, pointer, offset, reasoner,
							muteErrorSideEffects, source);

					newPtr0 = result.left.value;
					newRef = universe.arrayElementReference(
							symbolicUtil.getSymRef(arrayPtr),
							universe.add(index, offset));
					newPtr1 = symbolicUtil.makePointer(scopeId, vid, newRef);
					result.left.value = universe.cond(inBound, newPtr0,
							newPtr1);
					return result;
				}
			} else if (!muteErrorSideEffects) {
				// Valid pointer addition condition: inBound || point-to the end
				// of the array:
				resultType = reasoner
						.valid(universe.or(inBound,
								universe.equals(totalOffset, extent)))
						.getResultType();
				if (resultType != ResultType.YES)
					state = errorLogger.logError(source, state, pid,
							symbolicAnalyzer.stateInformation(state),
							zeroOffset, resultType, ErrorKind.OUT_OF_BOUNDS,
							"Pointer addition results in an index out of bound error.\n"
									+ "Pointer value:" + pointer
									+ "\nOffset value:" + offset);
			}
		} else if (!muteErrorSideEffects)
			errorLogger.logSimpleError(source, state, process,
					symbolicAnalyzer.stateInformation(state), ErrorKind.POINTER,
					"Pointer addition on incomplete array");
		// For the cases that either the pointer addition results within the
		// same sub-array or error-side effects are muted, directly making a new
		// pointer by adding the given offset to the reference expression of the
		// given pointer:
		newRef = universe.arrayElementReference(
				symbolicUtil.getSymRef(arrayPtr), universe.add(index, offset));
		eval = new Evaluation(state,
				symbolicUtil.makePointer(scopeId, vid, newRef));
		return new Pair<>(eval, null);
	}

	/**
	 * <p>
	 * This is a Helper function for
	 * {@link Evaluator#evaluatePointerAdd(State, int, String, BinaryExpression, SymbolicExpression, NumericExpression)}
	 * . <br>
	 * 
	 * For the given pointer who has an {@link OffsetReference}, this method
	 * performs the pointer addition operation by adding the given offset to the
	 * OffsetReference.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the calling process
	 * @param pointer
	 *            The pointer operand in pointer-addition
	 * @param offset
	 *            The numeric operand in pointer-addition
	 * @param muteErrorSideEffects
	 *            This method will NOT report error side-effects iff this
	 *            parameter set to true.
	 * @param source
	 *            The {@link CIVLSource} associates to the pointer addition.
	 * @return The evaluation of the pointer addition operation
	 * @throws UnsatisfiablePathConditionException
	 *             Iff error side-effects unmutes and offset is neither one or
	 *             zero.
	 */
	protected Evaluation offsetReferenceAddition(State state, int pid,
			SymbolicExpression pointer, NumericExpression offset,
			boolean muteErrorSideEffects, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		OffsetReference offsetRef = (OffsetReference) symbolicUtil
				.getSymRef(pointer);
		NumericExpression oldOffset = offsetRef.getOffset();
		NumericExpression newOffset = universe.add(oldOffset, offset);
		Evaluation eval;

		if (!civlConfig.svcomp() && !muteErrorSideEffects) {
			BooleanExpression claim = universe.and(
					universe.lessThanEquals(zero, newOffset),
					universe.lessThanEquals(newOffset, one));
			BooleanExpression assumption = state.getPathCondition(universe);
			ResultType resultType = universe.reasoner(assumption).valid(claim)
					.getResultType();

			if (resultType != ResultType.YES) {
				state = errorLogger.logError(source, state, pid,
						symbolicAnalyzer.stateInformation(state), claim,
						resultType, ErrorKind.OUT_OF_BOUNDS,
						"Pointer addition results in out of bounds.\nobject pointer:"
								+ pointer + "\n" + "offset = " + offset);
			}
		}
		eval = new Evaluation(state, symbolicUtil.setSymRef(pointer,
				universe.offsetReference(offsetRef.getParent(), newOffset)));
		return eval;
	}

	/**
	 * *
	 * <p>
	 * This is a Helper function for
	 * {@link Evaluator#evaluatePointerAdd(State, int, String, BinaryExpression, SymbolicExpression, NumericExpression)}
	 * . <br>
	 * 
	 * For the given pointer who has an {@link IdentifyReference}, this method
	 * performs the pointer addition operation by adding the given offset to the
	 * IdentifyReference.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the calling process
	 * @param pointer
	 *            The pointer operand in pointer-addition
	 * @param offset
	 *            The numeric operand in pointer-addition
	 * @param muteErrorSideEffects
	 *            This method will NOT report error side-effects iff this
	 *            parameter set to true.
	 * @param source
	 *            The {@link CIVLSource} associates to the pointer addition.
	 * @return The evaluation of the pointer addition operation
	 * @throws UnsatisfiablePathConditionException
	 *             Iff error side-effects unmutes and offset is neither one or
	 *             zero.
	 */
	protected Evaluation identityReferenceAddition(State state, int pid,
			SymbolicExpression pointer, NumericExpression offset,
			boolean muteErrorSideEffects, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		BooleanExpression claim;
		BooleanExpression assumption;
		ResultType resultType;
		ReferenceExpression symRef = symbolicUtil.getSymRef(pointer);

		claim = universe.equals(zero, offset);
		assumption = state.getPathCondition(universe);
		resultType = universe.reasoner(assumption).valid(claim).getResultType();
		if (resultType.equals(ResultType.YES))
			return new Evaluation(state, pointer);
		claim = universe.equals(one, offset);
		assumption = state.getPathCondition(universe);
		resultType = universe.reasoner(assumption).valid(claim).getResultType();
		if (resultType.equals(ResultType.YES))
			return new Evaluation(state, symbolicUtil.makePointer(pointer,
					universe.offsetReference(symRef, one)));
		else {
			if (!muteErrorSideEffects)
				state = errorLogger.logError(source, state, pid,
						symbolicAnalyzer.stateInformation(state), claim,
						resultType, ErrorKind.OUT_OF_BOUNDS,
						"Pointer addition results in out of bounds.\nobject pointer:"
								+ pointer + "\noffset = " + offset);
			// recovered, invalid pointer cannot be dereferenced, but
			// execution is not suppose to stop here:
			return new Evaluation(state, symbolicUtil.makePointer(pointer,
					universe.offsetReference(symRef, offset)));
		}
	}

	/* ********************** Methods from Evaluator *********************** */

	@Override
	public Evaluation evaluate(State state, int pid, Expression expression,
			boolean checkUndefinedValue)
			throws UnsatisfiablePathConditionException {
		ExpressionKind kind = expression.expressionKind();
		Evaluation result;
		String process = state.getProcessState(pid).name();

		if (expression.hasConstantValue())
			return new Evaluation(state, expression.constantValue());
		switch (kind) {
			case ABSTRACT_FUNCTION_CALL :
				result = evaluateAbstractFunctionCall(state, pid,
						(AbstractFunctionCallExpression) expression);
				break;
			case ADDRESS_OF :
				result = evaluateAddressOf(state, pid,
						(AddressOfExpression) expression);
				break;
			case ARRAY_LAMBDA : {
				result = evaluateArrayLambda(state, pid,
						(ArrayLambdaExpression) expression);
				break;
			}
			case ARRAY_LITERAL :
				result = evaluateArrayLiteral(state, pid,
						(ArrayLiteralExpression) expression);
				break;
			case BINARY :
				result = evaluateBinary(state, pid, process,
						(BinaryExpression) expression);
				break;
			case BOOLEAN_LITERAL :
				result = evaluateBooleanLiteral(state, pid,
						(BooleanLiteralExpression) expression);
				break;
			case CAST :
				result = evaluateCast(state, pid, process,
						(CastExpression) expression);
				break;
			case CHAR_LITERAL :
				result = evaluateCharLiteral(state, pid,
						(CharLiteralExpression) expression);
				break;
			case COND :
				throw new CIVLInternalException(
						"Conditional expressions should "
								+ "be translated away by CIVL model builder ",
						expression.getSource());
			case DEREFERENCE :
				result = evaluateDereference(state, pid, process,
						(DereferenceExpression) expression);
				break;
			case DERIVATIVE :
				result = evaluateDerivativeCall(state, pid,
						(DerivativeCallExpression) expression);
				break;
			case DOMAIN_GUARD :
				result = evaluateDomainGuard(state, pid,
						(DomainGuardExpression) expression);
				break;
			case REC_DOMAIN_LITERAL :
				result = evaluateRecDomainLiteral(state, pid,
						(RecDomainLiteralExpression) expression);
				break;
			case DOT :
				result = evaluateDot(state, pid, process,
						(DotExpression) expression);
				break;
			case DYNAMIC_TYPE_OF :
				result = evaluateDynamicTypeOf(state, pid,
						(DynamicTypeOfExpression) expression);
				break;
			case FUNCTION_IDENTIFIER :
				result = evaluateFunctionIdentifierExpression(state, pid,
						(FunctionIdentifierExpression) expression);
				break;
			case FUNCTION_GUARD :
				result = evaluateFunctionGuard(state, pid, process,
						(FunctionGuardExpression) expression);
				break;
			case HERE_OR_ROOT :
				result = evaluateHereOrRootScope(state, pid,
						(HereOrRootExpression) expression);
				break;
			case INITIAL_VALUE :
				result = evaluateInitialValue(state, pid,
						(InitialValueExpression) expression);
				break;
			case INTEGER_LITERAL :
				result = evaluateIntegerLiteral(state, pid,
						(IntegerLiteralExpression) expression);
				break;
			case LAMBDA :
				result = evaluateLambda(state, pid,
						(LambdaExpression) expression);
				break;
			case MPI_CONTRACT_EXPRESSION :
				result = evaluateMPIContractExpression(state, pid, process,
						(MPIContractExpression) expression);
				break;
			case REAL_LITERAL :
				result = evaluateRealLiteral(state, pid,
						(RealLiteralExpression) expression);
				break;
			case REGULAR_RANGE :
				result = evaluateRegularRange(state, pid,
						(RegularRangeExpression) expression);
				break;
			case SCOPEOF :
				result = evaluateScopeofExpression(state, pid, process,
						(ScopeofExpression) expression);
				break;
			case SELF :
				result = evaluateSelf(state, pid, (SelfExpression) expression);
				break;
			case PROC_NULL :
				result = this.evaluateProcnull(state, pid,
						(ProcnullExpression) expression);
				break;
			case SIZEOF_TYPE :
				result = evaluateSizeofTypeExpression(state, pid,
						(SizeofTypeExpression) expression);
				break;
			case SIZEOF_EXPRESSION :
				result = evaluateSizeofExpressionExpression(state, pid,
						(SizeofExpression) expression);
				break;
			case STRUCT_OR_UNION_LITERAL :
				result = evaluateStructOrUnionLiteral(state, pid,
						(StructOrUnionLiteralExpression) expression);
				break;
			case SUBSCRIPT :
				result = evaluateSubscript(state, pid, process,
						(SubscriptExpression) expression);
				break;
			case SYSTEM_GUARD : {
				SystemGuardExpression systemGuard = (SystemGuardExpression) expression;
				CIVLFunction function = systemGuard.function();

				if (function.functionContract() != null) {
					Expression guard = function.functionContract().guard();

					if (guard != null)
						return evaluateGuardofSystemFunction(
								systemGuard.getSource(), state, pid,
								systemGuard.library(), function,
								systemGuard.arguments());
				}
				result = getSystemGuard(expression.getSource(), state, pid,
						systemGuard.library(),
						systemGuard.function().name().name(),
						systemGuard.arguments());
				break;
			}
			case UNARY :
				result = evaluateUnary(state, pid,
						(UnaryExpression) expression);
				break;
			case UNDEFINED_PROC :
				result = new Evaluation(state, modelFactory
						.undefinedValue(typeFactory.processSymbolicType()));
				break;
			case VARIABLE :
				result = evaluateVariable(state, pid, process,
						(VariableExpression) expression, checkUndefinedValue);
				break;
			case QUANTIFIER : {
				result = evaluateQuantifiedExpression(state, pid,
						(QuantifiedExpression) expression);
				break;
			}
			case FUNC_CALL :
				result = evaluateFunctionCallExpression(state, pid,
						(FunctionCallExpression) expression);
				break;
			case STATE_REF :
				result = new Evaluation(state, modelFactory
						.stateValue(((StateExpression) expression).id()));
				break;
			case EXTENDED_QUANTIFIER :
				result = evaluateExtendedQuantifiedExpression(state, pid,
						(ExtendedQuantifiedExpression) expression);
				break;
			case MEMORY_UNIT :
			case NULL_LITERAL :
			case STRING_LITERAL :
				throw new CIVLSyntaxException(
						"Illegal use of " + kind + " expression: ",
						expression.getSource());
			case VALUE_AT :
			default :
				throw new CIVLInternalException("unreachable: " + kind,
						expression);
		}
		return result;
	}

	protected Evaluation evaluateQuantifiedExpression(State state, int pid,
			QuantifiedExpression expression)
			throws UnsatisfiablePathConditionException {
		return new QuantifiedExpressionEvaluator(modelFactory, stateFactory,
				libLoader, libExeLoader, symbolicUtil, symbolicAnalyzer,
				memUnitFactory, errorLogger, civlConfig)
						.evaluateQuantifiedExpression(state, pid,
								(QuantifiedExpression) expression);
	}

	protected Evaluation evaluateArrayLambda(State state, int pid,
			ArrayLambdaExpression arrayLambda)
			throws UnsatisfiablePathConditionException {
		return new QuantifiedExpressionEvaluator(modelFactory, stateFactory,
				libLoader, libExeLoader, symbolicUtil, symbolicAnalyzer,
				memUnitFactory, errorLogger, civlConfig)
						.evaluateArrayLambda(state, pid, arrayLambda);
	}

	protected Evaluation evaluateLambda(State state, int pid,
			LambdaExpression arrayLambda)
			throws UnsatisfiablePathConditionException {
		return new QuantifiedExpressionEvaluator(modelFactory, stateFactory,
				libLoader, libExeLoader, symbolicUtil, symbolicAnalyzer,
				memUnitFactory, errorLogger, civlConfig).evaluateLambda(state,
						pid, arrayLambda);
	}

	@SuppressWarnings("unchecked")
	protected boolean containsSymbolicConstant(SymbolicExpression expr,
			SymbolicConstant symbol) {
		if (expr instanceof SymbolicConstant)
			return expr.equals(symbol);

		int numArgs = expr.numArguments();

		for (int i = 0; i < numArgs; i++) {
			SymbolicObject arg = expr.argument(i);

			if (arg instanceof SymbolicExpression) {
				if (containsSymbolicConstant((SymbolicExpression) arg, symbol))
					return true;
			} else if (arg instanceof SymbolicSequence) {
				SymbolicSequence<SymbolicExpression> sequence = (SymbolicSequence<SymbolicExpression>) arg;
				int numEles = sequence.size();

				for (int j = 0; j < numEles; j++) {
					SymbolicExpression ele = sequence.get(j);

					if (containsSymbolicConstant(ele, symbol))
						return true;
				}
			}
		}
		return false;
	}

	protected Evaluation evaluateExtendedQuantifiedExpression(State state,
			int pid, ExtendedQuantifiedExpression extQuant)
			throws UnsatisfiablePathConditionException {
		return new QuantifiedExpressionEvaluator(modelFactory, stateFactory,
				libLoader, libExeLoader, symbolicUtil, symbolicAnalyzer,
				memUnitFactory, errorLogger, civlConfig)
						.evaluateExtendedQuantifiedExpression(state, pid,
								extQuant);
	}

	protected Evaluation evaluateFunctionCallExpression(State state, int pid,
			FunctionCallExpression expression)
			throws UnsatisfiablePathConditionException {
		return this.functionCallExecutor.evaluateAtomicPureFunction(state, pid,
				expression.callStatement());
	}

	@Override
	public Evaluation evaluateSizeofType(CIVLSource source, State state,
			int pid, CIVLType type) throws UnsatisfiablePathConditionException {
		Evaluation eval;

		if (type instanceof CIVLPrimitiveType) {
			NumericExpression value = ((CIVLPrimitiveType) type).getSizeof();
			BooleanExpression facts = ((CIVLPrimitiveType) type).getFacts();
			BooleanExpression pc = state.getPathCondition(universe);
			Reasoner reasoner = universe.reasoner(pc);

			if (!reasoner.isValid(facts)) {
				facts = universe.and(facts, pc);
				state = stateFactory.addToPathcondition(state, pid, facts);
			} else
				facts = pc;
			eval = new Evaluation(state, value);
		} else if (type instanceof CIVLCompleteArrayType) {
			NumericExpression extentValue;

			eval = evaluate(state, pid,
					((CIVLCompleteArrayType) type).extent());
			extentValue = (NumericExpression) eval.value;
			eval = evaluateSizeofType(source, eval.state, pid,
					((CIVLArrayType) type).elementType());
			eval.value = universe.multiply(extentValue,
					(NumericExpression) eval.value);
		} else if (type instanceof CIVLArrayType) {
			throw new CIVLInternalException(
					"sizeof applied to incomplete array type", source);
		} else {
			NumericExpression sizeof;

			eval = dynamicTypeOf(state, pid, type, source, false);
			sizeof = (NumericExpression) universe.apply(sizeofFunction,
					new Singleton<SymbolicExpression>(eval.value));
			eval.value = sizeof;
			eval.state = stateFactory.addToPathcondition(eval.state, pid,
					universe.lessThan(zero, sizeof));
		}
		return eval;
	}

	@Override
	public Triple<State, CIVLFunction, Integer> evaluateFunctionIdentifier(
			State state, int pid, Expression functionIdentifier,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		CIVLFunction function;
		Evaluation eval = this.evaluate(state, pid, functionIdentifier);
		int scopeId = symbolicUtil.getDyscopeId(source, eval.value);
		int fid = symbolicUtil.getVariableId(source, eval.value);
		// String funcName = "";
		Scope containingScope;

		if (scopeId < 0) {
			ProcessState procState = state.getProcessState(pid);

			errorLogger.logSimpleError(source, state,
					procState.name() + "(id=" + pid + ")",
					symbolicAnalyzer.stateInformation(state),
					ErrorKind.MEMORY_LEAK,
					"invalid function pointer: " + functionIdentifier);
			throw new UnsatisfiablePathConditionException();
		}
		state = eval.state;
		containingScope = state.getDyscope(scopeId).lexicalScope();
		function = containingScope.getFunction(fid);
		return new Triple<>(state, function, scopeId);
	}

	@Override
	public CIVLErrorLogger errorLogger() {
		return this.errorLogger;
	}

	@Override
	public Evaluation dereference(CIVLSource source, State state,
			String process, CIVLType referredType, SymbolicExpression pointer,
			boolean checkOutput, boolean strict)
			throws UnsatisfiablePathConditionException {
		boolean muteErrorSideEffects = false; // report error side effects

		return dereferenceWorker(source, state, process, referredType, pointer,
				checkOutput, false, strict, muteErrorSideEffects);
	}

	/**
	 * * Only three types (represented differently in CIVL) of the symbolic
	 * expression "charPointer" is acceptable:<br>
	 * A pointer to char <br>
	 * A pointer to an element of array of char. (e.g. char a[N][M]; a[x] or
	 * &a[x][0] are acceptable. Address of an element of array of char or
	 * pointer to an array of char are same as this situation.)<br>
	 * A complete char array
	 * 
	 * @param source
	 *            The CIVL source of the pointer to char expression
	 * @param state
	 *            The current state
	 * @param process
	 *            The identifier of the process
	 * @param charPointer
	 *            The pointer to char
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	@Override
	public Triple<State, StringBuffer, Boolean> getString(CIVLSource source,
			State state, String process, Expression charPointerExpr,
			SymbolicExpression charPointer)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression originalArray = null;
		SymbolicOperator operator = charPointer.operator();
		int int_arrayIndex = -1;
		StringBuffer result = new StringBuffer();

		if (operator == SymbolicOperator.ARRAY) {// string literal
			originalArray = charPointer;
			int_arrayIndex = 0;
		} else if (operator == SymbolicOperator.TUPLE) {
			ReferenceExpression ref = null;
			Evaluation eval;

			ref = symbolicUtil.getSymRef(charPointer);
			if (ref instanceof ArrayElementReference) {
				SymbolicExpression pointerCharArray = symbolicUtil
						.parentPointer(charPointer);
				SymbolicExpression charArray;

				eval = dereference(source, state, process,
						typeFactory.incompleteArrayType(typeFactory.charType()),
						pointerCharArray, false, true);
				state = eval.state;
				charArray = eval.value;
				originalArray = charArray;
				int_arrayIndex = symbolicUtil.extractInt(source,
						((ArrayElementReference) ref).getIndex());

			} else {
				eval = dereference(source, state, process,
						typeFactory.charType(), charPointer, false, true);
				state = eval.state;
				// A single character is not acceptable.
				if (eval.value.numArguments() <= 1) {
					this.errorLogger.logSimpleError(source, state, process,
							this.symbolicAnalyzer.stateInformation(state),
							ErrorKind.OTHER,
							"Try to obtain a string from a sequence of char has length"
									+ " less than or equal to one");
					throw new UnsatisfiablePathConditionException();
				} else {
					originalArray = eval.value;
					int_arrayIndex = 0;
				}
			}
		} else
			throw new CIVLUnimplementedFeatureException(
					"access on a non-concrete string", source);
		if (originalArray.operator() != SymbolicOperator.ARRAY)
			result.append(symbolicAnalyzer.symbolicExpressionToString(source,
					state, null, originalArray));
		else
			result = symbolicUtil.charArrayToString(source, originalArray,
					int_arrayIndex, false);
		return new Triple<>(state, result, true);
		// if (charPointer.operator() == SymbolicOperator.ARRAY) {
		// // SymbolicSequence<?> originalArray = null;
		// StringBuffer result = new StringBuffer();
		// ReferenceExpression ref = null;
		// Evaluation eval;
		//
		// if (charPointer.type() instanceof SymbolicCompleteArrayType) {
		// originalArray = charPointer;
		// int_arrayIndex = 0;
		// } else {
		// ref = symbolicUtil.getSymRef(charPointer);
		// if (ref instanceof ArrayElementReference) {
		// SymbolicExpression pointerCharArray = symbolicUtil
		// .parentPointer(source, charPointer);
		// SymbolicExpression charArray;
		//
		// eval = dereference(source, state, process, null,
		// pointerCharArray, false);
		// state = eval.state;
		// charArray = eval.value;
		// originalArray = charArray;
		// int_arrayIndex = symbolicUtil.extractInt(source,
		// ((ArrayElementReference) ref).getIndex());
		//
		// } else {
		// eval = dereference(source, state, process, charPointerExpr,
		// charPointer, false);
		// state = eval.state;
		// // A single character is not acceptable.
		// if (eval.value.numArguments() <= 1) {
		// this.errorLogger.logSimpleError(source, state, process,
		// this.symbolicAnalyzer.stateInformation(state),
		// ErrorKind.OTHER,
		// "Try to obtain a string from a sequence of char has length"
		// + " less than or equal to one");
		// throw new UnsatisfiablePathConditionException();
		// } else {
		// originalArray = eval.value;
		// int_arrayIndex = 0;
		// }
		// }
		// }
		// result = symbolicUtil.charArrayToString(source, originalArray,
		// int_arrayIndex, false);
		// return new Triple<>(state, result, true);
		// } else
		// throw new CIVLUnimplementedFeatureException(
		// "access on a non-concrete string", source);
	}

	@Override
	public Evaluation getStringExpression(State state, String process,
			CIVLSource source, SymbolicExpression charPointer)
			throws UnsatisfiablePathConditionException {
		BooleanExpression pc = state.getPathCondition(universe);
		Reasoner reasoner = universe.reasoner(pc);
		ReferenceExpression symRef = symbolicUtil.getSymRef(charPointer);

		if (symRef.isArrayElementReference()) {
			ArrayElementReference arrayEltRef = (ArrayElementReference) symRef;
			SymbolicExpression arrayReference = symbolicUtil
					.parentPointer(charPointer);
			NumericExpression indexExpr = arrayEltRef.getIndex();
			Evaluation eval = dereference(source, state, process,
					typeFactory.incompleteArrayType(typeFactory.charType()),
					arrayReference, false, true);
			int index;

			if (indexExpr.isZero())
				index = 0;
			else {
				IntegerNumber indexNum = (IntegerNumber) reasoner
						.extractNumber(indexExpr);

				if (indexNum == null)
					throw new CIVLUnimplementedFeatureException(
							"access an element of an array of char with a non-concrete index",
							source);
				index = indexNum.intValue();
			}
			if (index == 0)
				return eval;
			else if (index > 0) {
				SymbolicExpression arrayValue = eval.value;
				SymbolicArrayType arrayType = (SymbolicArrayType) arrayValue
						.type();
				LinkedList<SymbolicExpression> charExprList = new LinkedList<>();
				int length;

				if (arrayType.isComplete()) {
					NumericExpression extent = ((SymbolicCompleteArrayType) arrayType)
							.extent();
					IntegerNumber extentNum = (IntegerNumber) reasoner
							.extractNumber(extent);

					if (extentNum == null)
						throw new CIVLUnimplementedFeatureException(
								"pointer into string of non-concrete length",
								source);
					length = extentNum.intValue();
				} else
					throw new CIVLUnimplementedFeatureException(
							"pointer into string of unknown length", source);
				for (int i = index; i < length; i++) {
					SymbolicExpression charExpr = universe.arrayRead(arrayValue,
							universe.integer(i));

					charExprList.add(charExpr);
					// if you wanted to get heavy-weight, call the prover to see
					// if charExpr equals the null character instead of this:
					if (nullCharExpr.equals(charExpr))
						break;
				}
				eval.value = universe.array(charType, charExprList);
				return eval;
			} else
				throw new CIVLInternalException(
						"negative pointer index: " + index, source);
		}
		throw new CIVLUnimplementedFeatureException(
				"pointer to char is not into an array of char", source);
	}

	@Override
	public ModelFactory modelFactory() {
		return modelFactory;
	}

	@Override
	public Evaluation evaluatePointerAdd(State state, int pid, String process,
			BinaryExpression expression, SymbolicExpression pointer,
			NumericExpression offset)
			throws UnsatisfiablePathConditionException {
		Pair<BooleanExpression, ResultType> checkPointer = symbolicAnalyzer
				.isDefinedPointer(state, pointer, expression.getSource());

		if (checkPointer.right != ResultType.YES) {
			errorLogger.logError(expression.getSource(), state, pid,
					symbolicAnalyzer.stateInformation(state), checkPointer.left,
					checkPointer.right, ErrorKind.DEREFERENCE,
					"Attempt to perform pointer addition upon an undefined pointer");
			throw new UnsatisfiablePathConditionException();
		} else {
			ReferenceExpression symRef = symbolicUtil.getSymRef(pointer);

			if (symRef.isArrayElementReference()) {
				return arrayElementReferenceAddWorker(state, pid, pointer,
						offset, false, expression.left().getSource()).left;
			} else if (symRef.isOffsetReference()) {
				return offsetReferenceAddition(state, pid, pointer, offset,
						false, expression.getSource());
			} else if (symRef.isIdentityReference()) {
				return identityReferenceAddition(state, pid, pointer, offset,
						false, expression.getSource());
			} else
				throw new CIVLUnimplementedFeatureException(
						"Pointer addition for anything other than array elements or variables",
						expression);
		}
	}

	@Override
	public Evaluation pointerSubtraction(State state, int pid, String process,
			BinaryExpression expression, SymbolicExpression leftPtr,
			SymbolicExpression rightPtr)
			throws UnsatisfiablePathConditionException {
		int leftVid, leftSid, rightVid, rightSid;
		SymbolicExpression arrayPtr;
		NumericExpression leftPos = zero, rightPos = zero;
		NumericExpression[] leftPtrIndices, rightPtrIndices;
		NumericExpression[] arraySliceSizes;

		// ModelFactory already checked type compatibility, so here we just
		// check if these two pointers are pointing to same object and array
		// element reference pointers.
		leftVid = symbolicUtil.getVariableId(expression.left().getSource(),
				leftPtr);
		leftSid = symbolicUtil.getDyscopeId(expression.left().getSource(),
				leftPtr);
		rightVid = symbolicUtil.getVariableId(expression.right().getSource(),
				rightPtr);
		rightSid = symbolicUtil.getDyscopeId(expression.right().getSource(),
				rightPtr);

		if (rightSid == -1 && rightVid == -1) {
			// offset subtraction
			return new Evaluation(state,
					this.symbolicAnalyzer.pointerArithmetics(
							expression.getSource(), state, true, leftPtr,
							rightPtr));
		} else {
			// Check if the two point to the same object
			if ((rightVid != leftVid) || (rightSid != leftSid)) {
				state = errorLogger.logError(expression.getSource(), state, pid,
						symbolicAnalyzer.stateInformation(state), null,
						ResultType.NO, ErrorKind.POINTER,
						"Operands of pointer subtraction don't point to the "
								+ "same obejct");
				throw new UnsatisfiablePathConditionException();
			}
			// Check if two pointers are array element reference pointers. Based
			// on
			// C11 Standard 6.5.6, entry 9: When two pointers are subtracted,
			// both
			// shall point to elements of the same array object, or one past the
			// last element of the array object; the result is the difference of
			// the
			// subscripts of the two array elements.
			// Thus, any pointer which is not an array element reference is
			// invalid
			// for pointer subtraction.
			if (!(symbolicUtil.getSymRef(leftPtr).isArrayElementReference()
					&& symbolicUtil.getSymRef(rightPtr)
							.isArrayElementReference()))
				state = errorLogger.logError(expression.getSource(), state, pid,
						symbolicAnalyzer.stateInformation(state), null,
						ResultType.NO, ErrorKind.POINTER,
						"Not both of the operands of pointer subtraction points to an array element");
			// Get the pointer to the whole array
			arrayPtr = symbolicUtil.arrayRootPtr(leftPtr);
			leftPtrIndices = symbolicUtil.extractArrayIndicesFrom(leftPtr);
			rightPtrIndices = symbolicUtil.extractArrayIndicesFrom(rightPtr);
			// If the two pointers are pointing to heap, check if they are
			// pointing to the same memory block:
			if (leftVid == 0 && !symbolicUtil.arePoint2SameMemoryBlock(leftPtr,
					rightPtr)) {
				state = errorLogger.logError(expression.getSource(), state, pid,
						symbolicAnalyzer.stateInformation(state), null,
						ResultType.NO, ErrorKind.POINTER,
						"Operands of pointer subtraction point to different heap obejcts");
			}
			// Get array by dereferencing array pointer
			SymbolicType arrayType = symbolicAnalyzer.dynamicTypeOfObjByPointer(
					expression.getSource(), state, arrayPtr);

			assert arrayType != null
					&& arrayType.typeKind() == SymbolicTypeKind.ARRAY
					&& arrayType instanceof SymbolicCompleteArrayType;
			arraySliceSizes = symbolicUtil
					.arraySlicesSizes(symbolicUtil.arrayDimensionExtents(
							(SymbolicCompleteArrayType) arrayType));
			for (int i = leftPtrIndices.length, j = arraySliceSizes.length
					- 1; --i >= 0; j--) {
				NumericExpression leftIdx, rightIdx;
				NumericExpression sliceSizes = arraySliceSizes[j];

				leftIdx = leftPtrIndices[i];
				rightIdx = rightPtrIndices[i];
				leftPos = universe.add(leftPos,
						universe.multiply(leftIdx, sliceSizes));
				rightPos = universe.add(rightPos,
						universe.multiply(rightIdx, sliceSizes));
			}
			return new Evaluation(state, universe.subtract(leftPos, rightPos));
		}
	}

	@Override
	public Evaluation reference(State state, int pid, LHSExpression operand)
			throws UnsatisfiablePathConditionException {
		Evaluation result;

		if (operand instanceof VariableExpression) {
			Variable variable = ((VariableExpression) operand).variable();
			int sid = state.getDyscopeID(pid, variable);
			int vid = variable.vid();

			result = new Evaluation(state,
					symbolicUtil.makePointer(sid, vid, identityReference));
		} else if (operand instanceof SubscriptExpression) {
			LHSExpression arrayExpr = ((SubscriptExpression) operand).array();
			Evaluation refEval = reference(state, pid, arrayExpr);
			SymbolicExpression arrayPointer = refEval.value;
			ReferenceExpression oldSymRef = symbolicUtil
					.getSymRef(arrayPointer);
			NumericExpression index;
			ReferenceExpression newSymRef;
			SymbolicExpression array;
			SymbolicArrayType arrayType;

			result = evaluate(refEval.state, pid,
					((SubscriptExpression) operand).index());
			index = (NumericExpression) result.value;
			result = dereference(operand.getSource(), state,
					state.getProcessState(pid).name(),
					arrayExpr.getExpressionType(), arrayPointer, false, true);
			array = result.value;
			arrayType = (SymbolicArrayType) array.type();
			if (array.type() == null)
				arrayType = (SymbolicArrayType) arrayExpr.getExpressionType()
						.getDynamicType(universe);
			if (!operand.isErrorFree())
				result.state = this.checkArrayIndexInBound(state, pid,
						operand.getSource(), arrayType, array, index, true);
			newSymRef = universe.arrayElementReference(oldSymRef, index);
			result.value = symbolicUtil.setSymRef(arrayPointer, newSymRef);
		} else if (operand instanceof DereferenceExpression) {
			// &(*p) = p, so just evaluate the pointer and return.
			result = evaluate(state, pid,
					((DereferenceExpression) operand).pointer());
		} else if (operand instanceof DotExpression) {
			DotExpression dot = (DotExpression) operand;
			int index = dot.fieldIndex();

			Evaluation eval = reference(state, pid,
					(LHSExpression) dot.structOrUnion());
			SymbolicExpression structPointer = eval.value;
			ReferenceExpression oldSymRef = symbolicUtil
					.getSymRef(structPointer);
			ReferenceExpression newSymRef;

			if (dot.isStruct()) {
				newSymRef = universe.tupleComponentReference(oldSymRef,
						universe.intObject(index));
			} else {
				newSymRef = universe.unionMemberReference(oldSymRef,
						universe.intObject(index));
			}
			eval.value = symbolicUtil.setSymRef(structPointer, newSymRef);
			result = eval;
		} else
			throw new CIVLInternalException("Unknown kind of LHSExpression",
					operand);
		return result;
	}

	public StateFactory stateFactory() {
		return stateFactory;
	}

	@Override
	public SymbolicUtility symbolicUtility() {
		return symbolicUtil;
	}

	public SymbolicUniverse universe() {
		return universe;
	}

	@Override
	public Pair<Evaluation, NumericExpression[]> arrayElementReferenceAdd(
			State state, int pid, SymbolicExpression ptr,
			NumericExpression offset, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression newPtr = symbolicUtil.makePointer(ptr,
				symbolicAnalyzer.getLeafNodeReference(state, ptr, source));

		return arrayElementReferenceAddWorker(state, pid, newPtr, offset, false,
				source);
	}

	@Override
	public List<ReferenceExpression> leafNodeReferencesOfType(CIVLSource source,
			State state, int pid, CIVLType type)
			throws UnsatisfiablePathConditionException {
		return this.leafNodeReferencesOfType(source, state, pid, type,
				universe.identityReference());
	}

	private List<ReferenceExpression> leafNodeReferencesOfType(
			CIVLSource source, State state, int pid, CIVLType type,
			ReferenceExpression parent)
			throws UnsatisfiablePathConditionException {
		List<ReferenceExpression> result = new ArrayList<>();
		TypeKind typeKind = type.typeKind();

		switch (typeKind) {
			case ARRAY :
				throw new CIVLUnimplementedFeatureException(
						"sub-references of incomplete arrays", source);

			case COMPLETE_ARRAY : {
				CIVLCompleteArrayType arrayType = (CIVLCompleteArrayType) type;
				Expression extent = arrayType.extent();
				Evaluation eval = this.evaluate(state, pid, extent);
				NumericExpression extentValue = (NumericExpression) eval.value;
				CIVLType eleType = arrayType.elementType();

				state = eval.state;

				Reasoner reasoner = universe
						.reasoner(state.getPathCondition(universe));
				IntegerNumber length_number = (IntegerNumber) reasoner
						.extractNumber(extentValue);

				if (length_number != null) {
					int length_int = length_number.intValue();

					for (int i = 0; i < length_int; i++) {
						ArrayElementReference arrayEle = universe
								.arrayElementReference(parent,
										universe.integer(i));

						result.addAll(this.leafNodeReferencesOfType(source,
								state, pid, eleType, arrayEle));
					}
				} else
					throw new CIVLUnimplementedFeatureException(
							"sub-references of arrays with non-concrete extent",
							source);
				break;
			}
			case DOMAIN :
			case ENUM :
			case POINTER :
			case BUNDLE :
			case PRIMITIVE :
				result.add(parent);
				break;
			case STRUCT_OR_UNION : {
				CIVLStructOrUnionType structOrUnion = (CIVLStructOrUnionType) type;
				int numFields = structOrUnion.numFields();

				if (structOrUnion.isUnionType())
					throw new CIVLUnimplementedFeatureException(
							"sub-references of union type", source);
				for (int i = 0; i < numFields; i++) {
					CIVLType filedType = structOrUnion.getField(i).type();
					TupleComponentReference tupleComp = universe
							.tupleComponentReference(parent,
									universe.intObject(i));

					result.addAll(this.leafNodeReferencesOfType(source, state,
							pid, filedType, tupleComp));
				}
				break;
			}
			default :
				throw new CIVLUnimplementedFeatureException(
						"sub-references of " + typeKind, source);
		}
		return result;
	}

	@Override
	public Pair<State, SymbolicArrayType> evaluateCIVLArrayType(State state,
			int pid, CIVLArrayType type)
			throws UnsatisfiablePathConditionException {
		Pair<State, SymbolicArrayType> ret_pair;
		Evaluation eval;
		NumericExpression extent;

		if (!type.isComplete()) {
			// since type is CIVLArrayType, following cast should be safe.
			ret_pair = new Pair<>(state,
					(SymbolicArrayType) type.getDynamicType(universe));
			return ret_pair;
		}
		// if type is complete array type, get extent.
		eval = this.evaluate(state, pid,
				((CIVLCompleteArrayType) type).extent());
		extent = (NumericExpression) eval.value;
		if (!type.elementType().isArrayType()) {
			SymbolicArrayType ret_type = universe.arrayType(
					type.elementType().getDynamicType(universe), extent);

			state = eval.state;
			ret_pair = new Pair<>(state, ret_type);
			return ret_pair;
		} else {
			SymbolicArrayType ret_type;

			// This branch comes from
			// "if element type of 'type' has an array type", so following cast
			// is safe.
			ret_pair = this.evaluateCIVLArrayType(state, pid,
					(CIVLArrayType) type.elementType());
			ret_type = universe.arrayType(ret_pair.right, extent);
			ret_pair.right = ret_type;
			return ret_pair;
		}
	}

	@Override
	public MemoryUnitExpressionEvaluator memoryUnitEvaluator() {
		return memUnitEvaluator;
	}

	/**
	 * <p>
	 * <strong>pre-condition:</strong>
	 * <ol>
	 * <li>The given pointer must point to an array element of a complete array
	 * object.</li>
	 * </ol>
	 * </p>
	 * 
	 * <p>
	 * Updates index informations of {@link ArrayElementReference}s in the given
	 * pointer, results in a new pointer which is the result of the pointer
	 * arithmetic operation. The given pointer can be represented as the address
	 * of the first element in the array plus an offset which depends on the
	 * position of the element: <code>
	 * Array being pointed: a[e<sub>0</sub>][e<sub>..</sub>][e<sub>n-1</sub>], 
	 * where e<sub>i</sub> represents the extent of the i-th dimension.
	 * 
	 * Pointer p = &a[0][..][0] + 
	 *             \sum(0, n-2, \lambda int j;
	 *                                 idx<sub>j</sub> * \product(j+1, n-1, \lambda int i; e<sub>i</sub>)
	 *                 ) + idx<sub>n-1</sub>;
	 * where we borrows the fold notation of ACSL and idx<sub>i</sub> is the index of element in i-th dimension.
	 * 
	 * Lets use a symbol X = \sum(0, n-2, \lambda int j;
	 *                                 idx<sub>j</sub> * \product(j+1, n-1, \lambda int i; e<sub>i</sub>)
	 *                           ) + idx<sub>n-1</sub>;
	 * 
	 * For the pointer arithmetic: p + offset = &a[0][..][0] + (X + offset);, it eventually points to 
	 * an element (<strong>the element will not necessarily exist</strong>) with indices:
	 * 
	 * idx<sub>i</sub> = (  (X + offset) - \sum(0, i-1, \lambda int j; 
	 *                                            idx<sub>j</sub> * \product(j+1, n-1, \lambda int k; e<sub>k</sub>)
	 *                                         )
	 *                   ) / \product(i+1, n-1, \lambda int k; e<sub>k</sub>)
	 * 
	 *  </code>
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The String identifier of the process
	 * @param pointedVid
	 *            The variable id of the pointed array object
	 * @param pointedSid
	 *            The variable id of the pointed array object
	 * @param pointer
	 *            The pointer points to the array object
	 * @param offset
	 *            The offset added to the pointer
	 * @param reasoner
	 *            An instance reference of a {@link Reasoner} object
	 * @param source
	 *            The CIVLSource of the statement
	 * @return A pair of an evaluation, which is the evaluation of the array
	 *         element-reference addition, and an array of sizes of each
	 *         dimensional slice of the referred array object, the order of
	 *         sizes of the dimensional slices is from larger ones to smaller
	 *         ones.
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Pair<Evaluation, NumericExpression[]> recomputeArrayIndices(
			State state, int pid, int pointedVid, int pointedSid,
			SymbolicExpression pointer, NumericExpression offset,
			Reasoner reasoner, boolean muteErrorSideEffects, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		NumericExpression totalOffset = zero;
		NumericExpression sliceSize = one;
		SymbolicExpression arrayRootPtr;
		NumericExpression[] indices, arrayExtents, sliceSizes, oldIndices;
		ReferenceExpression newRef;
		SymbolicType dyType;
		SymbolicCompleteArrayType dyarrayType;
		Evaluation eval;
		int dim;

		arrayRootPtr = symbolicUtil.arrayRootPtr(pointer);
		dyType = symbolicAnalyzer.dynamicTypeOfObjByPointer(source, state,
				arrayRootPtr);
		assert dyType != null && dyType instanceof SymbolicArrayType
				&& ((SymbolicArrayType) dyType).isComplete();
		dyarrayType = (SymbolicCompleteArrayType) dyType;
		arrayExtents = symbolicUtil.arrayDimensionExtents(dyarrayType);
		sliceSizes = symbolicUtil.arraySlicesSizes(arrayExtents);
		dim = dyarrayType.dimensions();
		oldIndices = symbolicUtil.extractArrayIndicesFrom(pointer);
		assert oldIndices.length <= dim && sliceSizes.length == dim;
		// computes total offset from the first element
		for (int i = 0; i < oldIndices.length; i++) {
			NumericExpression oldIndex;

			oldIndex = oldIndices[i];
			sliceSize = sliceSizes[i];
			totalOffset = universe.add(totalOffset,
					universe.multiply(oldIndex, sliceSize));
		}
		totalOffset = universe.add(totalOffset, offset);

		// Computes new indexes
		Pair<State, NumericExpression[]> state_newIndices = recomputeArrayIndicesWorker(
				state, pid, dim, totalOffset, sliceSizes, arrayExtents,
				muteErrorSideEffects, source);

		indices = state_newIndices.right;
		newRef = symbolicUtil.makeArrayElementReference(
				symbolicUtil.getSymRef(arrayRootPtr), indices);
		eval = new Evaluation(state_newIndices.left,
				symbolicUtil.makePointer(pointedSid, pointedVid, newRef));
		return new Pair<>(eval, sliceSizes);
	}

	/**
	 * <p>
	 * The worker method for
	 * {@link #recomputeArrayIndices(State, int, int, int, SymbolicExpression, NumericExpression, Reasoner, boolean, CIVLSource)}
	 * . This method returns an updated state and an array of new indices.
	 * 
	 * Note that the compute of new indices is driven by pointer addition, so
	 * that they may point to the end of an array (different from array
	 * subscript which will not allow one to do that).
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the calling process
	 * @param dimensions
	 *            The number of dimensions of the array object whose element was
	 *            referred by the old indices.
	 * @param totalOffset
	 *            The total offset from the base address of the referred array
	 *            object to the element, which will be referred by the new
	 *            indices.
	 * @param arraySliceSizes
	 *            The size of each dimensional slice of the referred array
	 *            object.
	 * @param arrayExtents
	 *            The extent of each dimension of the referred array object.
	 * @param muteErrorSideEffects
	 *            This method will not report out-of-bound error iff this
	 *            parameter set to true.
	 * @param source
	 *            The {@link CIVLSource} associates to the pointer addition.
	 * @return A pair of an updated state and an array of new indices, the order
	 *         of the indices is same as the order of subscript.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Pair<State, NumericExpression[]> recomputeArrayIndicesWorker(
			State state, int pid, int dimensions, NumericExpression totalOffset,
			NumericExpression[] arraySliceSizes,
			NumericExpression[] arrayExtents, boolean muteErrorSideEffects,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		NumericExpression[] results = new NumericExpression[dimensions];
		Reasoner reasoner = universe.reasoner(state.getPathCondition(universe));
		ResultType resultType;
		BooleanExpression checkClaim;

		if (!muteErrorSideEffects) {
			NumericExpression arraySize = universe.multiply(arraySliceSizes[0],
					arrayExtents[0]);

			// totalOffset <= arraySize, e.g. T a[100], a + 100 is valid:
			checkClaim = universe.lessThanEquals(totalOffset, arraySize);
			checkClaim = universe.and(
					universe.lessThanEquals(zero, totalOffset), checkClaim);
			resultType = reasoner.valid(checkClaim).getResultType();
			if (resultType != ResultType.YES)
				state = errorLogger.logError(source, state, pid,
						symbolicAnalyzer.stateInformation(state), checkClaim,
						resultType, ErrorKind.OUT_OF_BOUNDS,
						"Pointer addition out-of-bound.\n" + "Base address + "
								+ totalOffset);
		}
		for (int i = 0; i < dimensions; i++) {
			Pair<NumericExpression, NumericExpression> newIndex_remainder;
			NumericExpression sliceSize = arraySliceSizes[i];
			NumericExpression newIndex;

			newIndex_remainder = symbolicUtil.arithmeticIntDivide(totalOffset,
					sliceSize);
			newIndex = newIndex_remainder.left;
			totalOffset = newIndex_remainder.right;
			if (i == dimensions - 1) { // no need check for the last index
				results[i] = newIndex;
				break;
			}
			// if new_index == extent, new_index--, offset += sliceSize:
			checkClaim = universe.equals(newIndex, arrayExtents[i]);
			resultType = reasoner.valid(checkClaim).getResultType();
			if (resultType == ResultType.YES) {
				newIndex = universe.subtract(newIndex, one);
				totalOffset = universe.add(totalOffset, arraySliceSizes[i]);
			} else if (resultType != ResultType.NO) {
				// Encoding conditional expressions for the unknown condition:
				// "remainder == 0 ?"
				newIndex = (NumericExpression) universe.cond(checkClaim,
						universe.subtract(newIndex, one), newIndex);
				totalOffset = (NumericExpression) universe.cond(checkClaim,
						universe.add(totalOffset, arraySliceSizes[i]),
						totalOffset);
			}
			results[i] = newIndex;
		}
		return new Pair<>(state, results);
	}

	/**
	 * <p>
	 * <b>Pre-condition: state must be a collate state, i.e. the state is
	 * obtained through a $collate_state handle and the calling process must be
	 * one of the participant processes of that collate state.</b>
	 * </p>
	 * <p>
	 * Evaluates an {@link MPIContractExpression}. It loads the
	 * {@link LibmpiEvaluator} to evaluates such an expression. see.
	 * {@link LibmpiEvaluator#evaluateMPIContractExpression(State, int, String, MPIContractExpression)}
	 * </p>
	 * 
	 * @param state
	 *            The state on where evaluation happens, the state must be a
	 *            collate state.
	 * @param pid
	 *            The pid of the process in the collate state
	 * @param process
	 *            The String identifier of the process
	 * @param expression
	 *            The {@link MPIContractExpression} that will evaluates
	 * @return An {@link Evaluation} of the expression
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateMPIContractExpression(State state, int pid,
			String process, MPIContractExpression expression)
			throws UnsatisfiablePathConditionException {
		LibmpiEvaluator mpiEvaluator;

		if (!civlConfig.isEnableMpiContract())
			throw new CIVLInternalException(
					"No MPI contract expression can be used without the enabling "
							+ "of MPI contract mode. To enable MPI contract mode, add the"
							+ " '-mpiContract' option to your civl verify command ",
					expression.getSource());
		try {
			mpiEvaluator = (LibmpiEvaluator) this.libLoader.getLibraryEvaluator(
					"mpi", this, modelFactory, symbolicUtil,
					this.symbolicAnalyzer);
			return mpiEvaluator.evaluateMPIContractExpression(state, pid,
					process, expression);
		} catch (LibraryLoaderException e) {
			this.errorLogger.logSimpleError(expression.getSource(), state,
					process, symbolicAnalyzer.stateInformation(state),
					ErrorKind.LIBRARY,
					"unable to load the library evaluator for the library "
							+ "mpi" + " for the MPI expression " + expression);
			throw new UnsatisfiablePathConditionException();
		}
	}

	@Override
	public SymbolicAnalyzer symbolicAnalyzer() {
		return this.symbolicAnalyzer;
	}

	@Override
	public Evaluation evaluate(State state, int pid, Expression expression)
			throws UnsatisfiablePathConditionException {
		return this.evaluate(state, pid, expression, true);
	}

	@Override
	public Evaluation havoc(State state, SymbolicType type) {
		Pair<State, SymbolicConstant> freshSymbol = this.stateFactory
				.getFreshSymbol(state, ModelConfiguration.HAVOC_PREFIX_INDEX,
						type);

		return new Evaluation(freshSymbol.left, freshSymbol.right);
	}

	@Override
	public void setConfiguration(CIVLConfiguration config) {
		this.civlConfig = config;
	}
}
