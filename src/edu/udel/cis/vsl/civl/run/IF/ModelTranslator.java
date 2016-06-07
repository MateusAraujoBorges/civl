package edu.udel.cis.vsl.civl.run.IF;

import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.bar;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.macroO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showProverQueriesO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showQueriesO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.sysIncludePathO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.userIncludePathO;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.AttributeKey;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.config.IF.Configuration;
import edu.udel.cis.vsl.abc.config.IF.Configuration.Architecture;
import edu.udel.cis.vsl.abc.config.IF.Configurations;
import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;
import edu.udel.cis.vsl.abc.front.IF.ParseException;
import edu.udel.cis.vsl.abc.front.IF.ParseTree;
import edu.udel.cis.vsl.abc.front.IF.Preprocessor;
import edu.udel.cis.vsl.abc.front.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.front.c.preproc.PreprocessorTokenSource;
import edu.udel.cis.vsl.abc.main.FrontEnd;
import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.abc.token.IF.CivlcTokenSource;
import edu.udel.cis.vsl.abc.token.IF.Macro;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.transform.IF.Transform;
import edu.udel.cis.vsl.abc.util.IF.MacroConstants;
import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.config.IF.CIVLConstants;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelBuilder;
import edu.udel.cis.vsl.civl.model.IF.Models;
import edu.udel.cis.vsl.civl.transform.IF.IntDivisionTransformer;
import edu.udel.cis.vsl.civl.transform.IF.TransformerFactory;
import edu.udel.cis.vsl.civl.transform.IF.Transforms;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.gmc.CommandLineException;
import edu.udel.cis.vsl.gmc.GMCConfiguration;
import edu.udel.cis.vsl.gmc.GMCSection;
import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

/**
 * A model translator parses, links, transforms a sequence of source files (C or
 * CIVL-C programs) into a ABC program; and then build a CIVL model from that
 * program. Command line options are also taken into account including macros,
 * transformer settings (e.g., -ompNoSimplify), input variables, system/user
 * include path, etc.
 * <p>
 * A model translator takes into account a command line section. E.g., the
 * command line
 * <code>civl compare -D_CIVL -spec -DN=5 sum.c -impl -DCUDA -inputNB=8 sum.c sum_cuda.c</code>
 * contains three command line sections the common section, the "spec" section
 * and the "impl" section. Two model translators will be invoked for translating
 * the specification and the implementation, respectively, taking into account
 * the common commandline section and the corresponding specific section
 * (different lists of files, different macros, input variables, etc).
 * <p>
 * Non-compare command line contains one command line section, and thus only one
 * model translator is created.
 * 
 * <p>
 * Orders of applying transformers:
 * <ol>
 * <li>Svcomp Transformer</li>
 * <li>General Transformer</li>
 * <li>IO Transformer</li>
 * <li>OpenMP Transformer, CUDA Transformer, Pthreads Transformer</li>
 * <li>MPI Transformer</li>
 * <li>Side-effect remover</li>
 * <li>Pruner</li>
 * </ol>
 * Note that for svcomp "*.i" programs, right before linking, the Pruner and the
 * Svcomp Unpreprocessing Transformer are applied to the "*.i" AST.
 * </p>
 * 
 * @author Manchun Zheng
 *
 */
public class ModelTranslator {

	// private final static fields (constants)
	/**
	 * The default macro for CIVL-C programs. Could be disable by the setting
	 * the option _CIVL to false: <code>-_CIVL=false</code>.
	 */
	private static final String CIVL_MACRO = "_CIVL";

	/**
	 * A macro for MPI contract features. Once the option "-mpiContrac" is set
	 * in command line, such a macro should be enabled.
	 */
	private static final String MPI_CONTRACT_MACRO = "_MPI_CONTRACT";

	/**
	 * An empty file array
	 */
	private final static File[] emptyFileArray = new File[0];

	/**
	 * The CIVL system include path for library implementations
	 */
	private final static File[] civlSysPathArray = new File[] { CIVLConstants.CIVL_INCLUDE_PATH };

	// package-private fields, which are accessed by UserInterface
	/**
	 * The GMC configuration that this model translator associates with.
	 */
	GMCConfiguration gmcConfig;

	/**
	 * The command line section for this model translator.
	 */
	GMCSection cmdSection;

	/**
	 * The CIVL configuration for this model translator, which is dependent on
	 * the command line section.
	 */
	CIVLConfiguration config;

	/**
	 * The symbolic universe.
	 */
	SymbolicUniverse universe;

	// private fields
	/**
	 * The list of files specified in the command line section for parsing and
	 * linking.
	 */
	private String[] filenames;
	/**
	 * The system include paths specified in the command line section.
	 */
	private File[] systemIncludes;

	/**
	 * The user include paths specified in the command line section.
	 */
	private File[] userIncludes;

	/**
	 * The map of macros of this model translator, including macros defined in
	 * the command line section and the default <code>_CIVL</code> macro if the
	 * option "-_CIVL" isn't disable.
	 */
	private Map<String, Macro> macroMaps;

	/**
	 * The ABC front end to be used.
	 */
	FrontEnd frontEnd;

	/**
	 * The output stream for printing error messages.
	 */
	private PrintStream out = System.out;

	/**
	 * The file name of the user file, which is the first file specified in the
	 * command line section.
	 */
	private String userFileName;

	/**
	 * The transformer factory which provides transformers.
	 */
	private TransformerFactory transformerFactory;

	/**
	 * The core name of teh user file.
	 */
	private String userFileCoreName;

	private Configuration abcConfiguration = Configurations.newMinimalConfiguration();
	
	private AttributeKey intDivMacroKey;

	// constructor
	/**
	 * Creates a new instance of model translator.
	 * 
	 * @param gmcConfig
	 *            The GMC configuration which corresponds to the command line.
	 * @param gmcSection
	 *            The GMC section which corresponds to the command line section
	 *            this model translator associates with.
	 * @param filenames
	 *            The list of file names for parsing, which are specified in the
	 *            command line.
	 * @param coreName
	 *            The core name of the user file. It is assumed that the first
	 *            file in the file list from the command line is the core user
	 *            file, which usually is the one that contains the main
	 *            function.
	 * @throws PreprocessorException
	 *             if there is a problem processing any macros defined in the
	 *             command line
	 */
	ModelTranslator(GMCConfiguration gmcConfig, GMCSection gmcSection, String[] filenames, String coreName)
			throws PreprocessorException {
		this(gmcConfig, gmcSection, filenames, coreName, SARL.newStandardUniverse());
	}

	/**
	 * Creates a new instance of model translator.
	 * 
	 * @param gmcConfig
	 *            The GMC configuration which corresponds to the command line.
	 * @param gmcSection
	 *            The GMC section which corresponds to the command line section
	 *            this model translator associates with.
	 * @param filenames
	 *            The list of file names for parsing, which are specified in the
	 *            command line.
	 * @param coreName
	 *            The core name of the user file. It is assumed that the first
	 *            file in the file list from the command line is the core user
	 *            file, which usually is the one that contains the main
	 *            function.
	 * @param universe
	 *            The symbolic universe, the unique one used by this run.
	 * @throws PreprocessorException
	 *             if there is a problem processing any macros defined in the
	 *             command line
	 */
	ModelTranslator(GMCConfiguration gmcConfig, GMCSection cmdSection, String[] filenames, String coreName,
			SymbolicUniverse universe) throws PreprocessorException {
		this.cmdSection = cmdSection;
		this.gmcConfig = gmcConfig;
		this.userFileCoreName = coreName;
		this.universe = universe;
		if (cmdSection.isTrue(showProverQueriesO))
			universe.setShowProverQueries(true);
		if (cmdSection.isTrue(showQueriesO))
			universe.setShowQueries(true);
		config = new CIVLConfiguration(cmdSection);
		this.filenames = filenames;
		userFileName = filenames[0];
		if (config.svcomp()) {
			abcConfiguration.setSvcomp(config.svcomp());
			abcConfiguration.setArchitecture(Architecture._32_BIT);
		}
		this.frontEnd = new FrontEnd(abcConfiguration);
		this.transformerFactory = Transforms.newTransformerFactory(frontEnd.getASTFactory());
		systemIncludes = this.getSysIncludes(cmdSection);
		userIncludes = this.getUserIncludes(cmdSection);
		macroMaps = getMacroMaps(this.getLanguageByFileName(userFileName));
	}

	// package private methods

	/**
	 * Builds the ABC program, based on the command line associated with this
	 * model translator, which include several steps: parsing, linking, applying
	 * transformers, etc.
	 * 
	 * @return the ABC program built by CIVL according to the command line
	 *         setting
	 * @throws PreprocessorException
	 *             if there is a problem preprocessing any source files.
	 * @throws SyntaxException
	 *             if there is a problem parsing the source files.
	 * @throws ParseException
	 *             if there is a problem parsing or linking the source files.
	 * @throws IOException
	 *             if there is a problem reading source files.
	 */
	Program buildProgram() throws PreprocessorException, SyntaxException, IOException, ParseException {
		List<Pair<Language, CivlcTokenSource>> tokenSources;
		List<AST> asts = null;
		Program program = null;
		long startTime, endTime;
		long totalTime;

		startTime = System.currentTimeMillis();
		tokenSources = this.preprocess();
		endTime = System.currentTimeMillis();
		if (config.showTime()) {
			totalTime = (endTime - startTime);
			out.println(totalTime + "ms:\tSUMARRY ANTLR preprocessor parsing to form preproc tree for "
					+ tokenSources.size() + " translation units");
		}
		asts = this.parseTokens(tokenSources);
		if (this.config.svcomp()) {
			AST userAST = asts.get(0);
			long svcompPPstart = System.currentTimeMillis();

			// parsing preprocessed .i file
			if (userFileName.endsWith(".i") || this.config.unpreproc()) {
				frontEnd.getStandardAnalyzer(Language.CIVL_C).clear(userAST);
				frontEnd.getStandardAnalyzer(Language.CIVL_C).analyze(userAST);
				userAST = Transform.newTransformer("prune", userAST.getASTFactory()).transform(userAST);
				if (config.showTime()) {
					totalTime = System.currentTimeMillis() - svcompPPstart;
					out.println(totalTime + "ms:\tapplying pruner for svcomp source " + userFileName);
				}
				svcompPPstart = System.currentTimeMillis();
				asts.set(0, transformerFactory.getSvcompUnPPTransformer().transform(userAST));
				if (config.showTime()) {
					totalTime = System.currentTimeMillis() - svcompPPstart;
					out.println(
							totalTime + "ms:\tapplying unpreprocessing transformer for svcomp source " + userFileName);
				}
			}
		}
		program = this.link(asts);
		startTime = System.currentTimeMillis();
		this.applyAllTransformers(program);
		endTime = System.currentTimeMillis();
		if (config.showTime()) {
			totalTime = (endTime - startTime);// / 1000;
			out.println(totalTime + "ms:\tSUMARRY applying transformers");
		}
		if (config.debugOrVerbose() || config.showAST()) {
			out.println(bar + "The AST after linking and applying transformer is:" + bar);
			program.getAST().print(out);
			out.println();
			out.flush();
		}
		if (config.debugOrVerbose() || config.showProgram()) {
			out.println(bar + "The program after linking and applying transformer is:" + bar);
			program.prettyPrint(out);
			out.println();
			out.flush();
		}
		if (config.debugOrVerbose() || config.showInputVars())
			this.printInputVariableNames(program);

		return program;
	}

	/**
	 * Parse, link, apply transformers and build CIVL-C model for a certain
	 * CIVL-C compiling task.
	 * 
	 * @return the CIVL-C model of this compiling task specified by the command
	 *         line
	 * @throws CommandLineException
	 *             if there is a problem interpreting the command line section
	 * @throws PreprocessorException
	 *             if there is a problem preprocessing any source files.
	 * @throws SyntaxException
	 *             if there is a problem parsing the source files.
	 * @throws ParseException
	 *             if there is a problem parsing or linking the source files.
	 * @throws IOException
	 *             if there is a problem reading source files.
	 */
	Model translate() throws PreprocessorException, CommandLineException, SyntaxException, ParseException, IOException {
		long startTime = System.currentTimeMillis();
		Program program = this.buildProgram();
		long endTime = System.currentTimeMillis();
		long totalTime;

		if (config.showTime()) {
			totalTime = (endTime - startTime);
			out.println(totalTime + "ms: total time for building the whole program");
		}
		if (program != null) {
			Model model;

			startTime = System.currentTimeMillis();
			model = this.buildModel(program);
			endTime = System.currentTimeMillis();
			if (config.showTime()) {
				totalTime = (endTime - startTime);
				out.println(totalTime + "ms: CIVL model builder builds model from program");
			}
			return model;
		}
		return null;
	}

	/**
	 * Obtains the input variables declared in the given program
	 * 
	 * @return the input variables declared in the given program
	 * @throws PreprocessorException
	 *             if there is a problem preprocessing any source files.
	 * @throws SyntaxException
	 *             if there is a problem parsing the source files.
	 * @throws ParseException
	 *             if there is a problem parsing or linking the source files.
	 * @throws IOException
	 *             if there is a problem reading source files.
	 */
	List<VariableDeclarationNode> getInputVariables()
			throws PreprocessorException, SyntaxException, ParseException, IOException {
		Program program;

		program = this.buildProgram();
		return this.inputVariablesOfProgram(program);
	}

	/**
	 * Builds a CIVL model from an ABC program, which is the result of parsing,
	 * linking and transforming source files.
	 * 
	 * @param program
	 *            the ABC program.
	 * @return the CIVL model representation of the given ABC program.
	 * @throws CommandLineException
	 *             if there is a problem in the format of input variable values
	 *             in the command line.
	 */
	Model buildModel(Program program) throws CommandLineException {
		Model model;
		ModelBuilder modelBuilder = Models.newModelBuilder(this.universe);
		String modelName = coreName(userFileName);
		boolean hasFscanf = TransformerFactory.hasFunctionCalls(program.getAST(), Arrays.asList("scanf", "fscanf"));

		model = modelBuilder.buildModel(cmdSection, program, modelName, config.debugOrVerbose(), out);
		model.setHasFscanf(hasFscanf);
		if (config.debugOrVerbose() || config.showModel()) {
			out.println(bar + "The CIVL model is:" + bar);
			model.print(out, config.debugOrVerbose());
			out.println();
			out.flush();
		}
		return model;
	}

	// private methods

	/**
	 * Prints the input variables declared in the given program to the output
	 * stream.
	 * 
	 * @param program
	 *            the program, which is the result of parsing, linking and
	 *            transforming.
	 */
	private void printInputVariableNames(Program program) {
		List<VariableDeclarationNode> inputVars = this.inputVariablesOfProgram(program);

		out.println(bar + " input variables of " + this.userFileCoreName + " " + bar);
		for (VariableDeclarationNode var : inputVars) {
			var.prettyPrint(out);
			out.println();
		}
		out.flush();
	}

	/**
	 * Gets the list of input variables declared in the given program.
	 * 
	 * @param program
	 *            the program, which is the result of parsing, linking and
	 *            transforming.
	 * @return the list of input variables declared in the given program.
	 */
	private List<VariableDeclarationNode> inputVariablesOfProgram(Program program) {
		LinkedList<VariableDeclarationNode> result = new LinkedList<>();
		ASTNode root = program.getAST().getRootNode();

		for (ASTNode child : root.children()) {
			if (child != null && child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
				VariableDeclarationNode variable = (VariableDeclarationNode) child;

				if (variable.getTypeNode().isInputQualified()) {
					result.add(variable);
				}
			}
		}
		return result;
	}

	/**
	 * Extracts from a string the "core" part of a filename by removing any
	 * directory prefixes and removing any file suffix. For example, invoking on
	 * "users/siegel/gcd/gcd1.cvl" will return "gcd1". This is the name used to
	 * name the model and other structures; it is used in the log, to name
	 * generated files, and for error reporting.
	 * 
	 * @param filename
	 *            a filename
	 * @return the core part of that filename
	 */
	private static String coreName(String filename) {
		String result = filename;
		char sep = File.separatorChar;
		int lastSep = filename.lastIndexOf(sep);
		int lastDot;

		if (lastSep >= 0)
			result = result.substring(lastSep + 1);
		lastDot = result.lastIndexOf('.');
		if (lastDot >= 0)
			result = result.substring(0, lastDot);
		return result;
	}

	/**
	 * Applies default transformers (pruner and side-effect remover) of the
	 * given program.
	 * 
	 * @param program
	 *            The result of compiling, linking and applying CIVL-specific
	 *            transformers to the input program.
	 * @param config
	 *            The CIVL configuration.
	 * @throws SyntaxException
	 *             if there are syntax error when applying the transformers
	 */
	private void applyDefaultTransformers(Program program) throws SyntaxException {
		// always apply pruner and side effect remover
		if (config.debugOrVerbose())
			this.out.println("Apply pruner...");
		// FIXME: don't use "prune" or "sef" explicitly
		program.applyTransformer("prune");
		if (config.debugOrVerbose())
			program.prettyPrint(out);
		if (config.debugOrVerbose())
			this.out.println("Apply side-effect remover...");
		program.applyTransformer("sef");
		if (config.debugOrVerbose())
			program.prettyPrint(out);
	}

	/**
	 * Applies CIVL-specific transformers (such as general, mpi, omp, io, etc)
	 * to a given program. The transformers to be applied are selected by
	 * analyzing the program. Currently, the rules are as follows.
	 * <ul>
	 * <li>io: stdio.h is present;</li>
	 * <li>omp: omp.h is present or there is some OpenMP pragma;</li>
	 * <li>mpi: mpi.h is present;</li>
	 * <li>pthread: pthread.h is present.</li>
	 * </ul>
	 * 
	 * @param fileName
	 *            The file name of the source program.
	 * @param program
	 *            The result of compiling and linking the source program.
	 * @param config
	 *            The CIVL configuration.
	 * @throws SyntaxException
	 *             if there are syntax error when applying the transformers
	 */
	private void applyTranslationTransformers(Program program) throws SyntaxException {
		ASTNode root = program.getAST().getRootNode();
		Set<String> headers = new HashSet<>();
		boolean isC = userFileName.endsWith(".c") || userFileName.endsWith(".i");
		boolean hasStdio = false, hasOmp = false, hasMpi = false, hasPthread = false, hasCuda = false;

		for (SourceFile sourceFile : program.getAST().getSourceFiles()) {
			String filename = sourceFile.getName();

			if (filename.endsWith(".h")) {
				headers.add(filename);
			}
		}
		if (headers.contains("stdio.h"))
			hasStdio = true;
		if (headers.contains("omp.h") || program.hasOmpPragma())
			hasOmp = true;
		if (isC && headers.contains("pthread.h"))
			hasPthread = true;
		if (isC && headers.contains("mpi.h"))
			hasMpi = true;
		if (headers.contains("cuda.h"))
			hasCuda = true;
		if (config.svcomp()) {
			if (config.debugOrVerbose())
				this.out.println("Apply svcomp transformer...");
			program.apply(transformerFactory.getSvcompTransformer());
		}
		// always apply general transformation.
		if (config.debugOrVerbose())
			this.out.println("Apply general transformer...");
		program.apply(transformerFactory.getGeneralTransformer());
		if (config.debugOrVerbose()) {
			program.prettyPrint(out);
		}
		if (hasStdio) {
			if (config.debugOrVerbose())
				this.out.println("Apply IO transformer...");
			program.apply(transformerFactory.getIOTransformer());
			if (config.debugOrVerbose()) {
				program.prettyPrint(out);
			}
		}
		if (hasOmp) {
			if (!config.ompNoSimplify()) {
				if (config.debugOrVerbose())
					this.out.println("Apply OpenMP simplifier...");
				program.apply(transformerFactory.getOpenMPSimplifier());
				if (config.debugOrVerbose())
					program.prettyPrint(out);
			}
			if (config.debugOrVerbose())
				this.out.println("Apply OpenMP Orphan transformer...");
			program.apply(transformerFactory.getOpenMPOrphanTransformer());
			if (config.debugOrVerbose())
				program.prettyPrint(out);
			if (config.debugOrVerbose())
				this.out.println("Apply OpenMP-2-CIVL transformer...");
			program.apply(transformerFactory.getOpenMP2CIVLTransformer(config));
			if (config.debugOrVerbose())
				program.prettyPrint(out);
		}
		if (hasPthread) {
			if (config.svcomp()) {
				if (config.debugOrVerbose())
					this.out.println("Apply Macro transformer for svcomp programs ...");
				program.apply(transformerFactory.getMacroTransformer());
				if (config.debugOrVerbose())
					program.prettyPrint(out);
			}
			if (config.debugOrVerbose())
				this.out.println("Apply Pthread transformer...");
			program.apply(transformerFactory.getPthread2CIVLTransformer());
			if (config.debugOrVerbose())
				program.prettyPrint(out);
		}
		if (config.isEnableMpiContract()) {
			if (config.debugOrVerbose())
				this.out.println("Apply Contract transformer...");
			program.apply(transformerFactory.getContractTransformer());
			if (config.debugOrVerbose())
				program.prettyPrint(out);
		}
		if (hasMpi) {
			if (config.debugOrVerbose())
				this.out.println("Apply MPI transformer...");
			program.apply(transformerFactory.getMPI2CIVLTransformer());
			if (config.debugOrVerbose())
				program.prettyPrint(out);
		}
		if (hasCuda) {
			if (config.debugOrVerbose())
				this.out.println("Apply Cuda transformer...");
			program.apply(transformerFactory.getCuda2CIVLTransformer());
			if (config.debugOrVerbose())
				program.prettyPrint(out);
		}
		IntDivisionTransformer intDivTransformer= (IntDivisionTransformer)transformerFactory.getIntDivTransformer();
		
		if(intDivMacroKey != null){
			intDivTransformer.setIntDivAttributeKey(intDivMacroKey);
			if (root.getAttribute(intDivMacroKey) != null)
				program.getAST().getRootNode().setAttribute(intDivMacroKey, root.getAttribute(intDivMacroKey));
		}
		program.apply(intDivTransformer);
	}

	/**
	 * Apply transformers of the program.
	 * 
	 * @param fileName
	 *            The file name of the input program.
	 * @param program
	 *            The result of compiling and linking the input program.
	 * @throws SyntaxException
	 *             if there are syntax errors when applying transformers
	 */
	private void applyAllTransformers(Program program) throws SyntaxException {
		this.applyTranslationTransformers(program);
		this.applyDefaultTransformers(program);
	}

	/**
	 * Links the user specified ASTs with the system implementations of
	 * libraries used in the AST. <br>
	 * For example, if the user specified ASTs are "civl verify driver.c cg.c"
	 * and the libraries used are math.c and stdlib.c, then the userASTs has two
	 * ASTs parsed from driver.c and cg.c respectively, and two additional
	 * library implementation ASTs for math.c (math.cvl) and stdlib.c
	 * (stdlib.cvl) respectively.
	 * 
	 * @param preprocessor
	 *            The preprocessor to be used for preprocessing all system
	 *            implementation of libraries used by the given AST.
	 * @param userAST
	 *            The AST to be linked.
	 * @return The program which is the result of linking the given AST and the
	 *         ASTs of system implementation of libraries used.
	 * @throws PreprocessorException
	 *             if there is a problem preprocessing any source files.
	 * @throws SyntaxException
	 *             if there is a problem parsing the source files.
	 * @throws ParseException
	 *             if there is a problem parsing or linking the source files.
	 * @throws IOException
	 *             if there is a problem reading source files.
	 */
	private Program link(List<AST> userASTs)
			throws PreprocessorException, SyntaxException, ParseException, IOException {
		ArrayList<AST> asts = new ArrayList<>();
		AST[] TUs;
		Program program;
		long startTime, endTime;
		long totalTime;

		asts.addAll(this.systemImplASTs(userASTs));
		asts.addAll(userASTs);
		TUs = new AST[asts.size()];
		asts.toArray(TUs);
		// for (AST ast : TUs){
		// System.out.println("hhh:"+ast.getMacroMap().keySet());
		// }
		if (config.debugOrVerbose()) {
			out.println("Linking: ");
			for (AST ast : TUs)
				out.println("  " + ast);
			out.flush();
		}
		startTime = System.currentTimeMillis();
		// TUs[0].prettyPrint(System.out, false);
		program = frontEnd.link(TUs, Language.CIVL_C);
		// System.out.println("haha2:"+program.getAST().getMacroMap().keySet());
		// program.prettyPrint(System.out);
		endTime = System.currentTimeMillis();
		if (config.showTime()) {
			totalTime = (endTime - startTime);// / 1000;
			out.println(totalTime + "ms:\tSUMARRY linking " + TUs.length + " ASTs");
		}
		return program;
	}

	/**
	 * Parses a given token source into an AST.
	 * 
	 * @param tokenSource
	 *            The token source to be parsed.
	 * @return The unanalyzed AST which is the result of parsing the given token
	 *         source.
	 * @throws SyntaxException
	 * @throws ParseException
	 */
	private AST parse(Language language, CivlcTokenSource tokenSource) throws SyntaxException, ParseException {
		ParseTree tree;
		AST ast;
		long startTime;
		long endTime;
		long totalTime;

		if (config.debugOrVerbose()) {
			out.println("Generating AST for " + tokenSource);
		}
		startTime = System.currentTimeMillis();
		tree = frontEnd.getParser(language).parse(tokenSource);
		endTime = System.currentTimeMillis();
		if (config.showTime()) {
			totalTime = (endTime - startTime);// / 1000;
			out.println(totalTime + "ms:\t\tANTLR parsing to form ANTLR tree for TU " + tokenSource);
		}
		startTime = System.currentTimeMillis();
		ast = frontEnd.getASTBuilder(language).getTranslationUnit(tree);
		endTime = System.currentTimeMillis();
		if (config.showTime()) {
			totalTime = (endTime - startTime);// / 1000;
			out.println(totalTime + "ms:\t\tconverting ANTLR tree to AST for TU " + tokenSource);
		}
		if (tokenSource instanceof PreprocessorTokenSource) {
			Map<String, Macro> macroMap = ((PreprocessorTokenSource) tokenSource).getMacroMap();
			ASTNode root = ast.getRootNode();

			if (macroMap.containsKey(MacroConstants.NO_CHECK_DIVISION_BY_ZERO)) {
				// TODO
				if(intDivMacroKey == null)
					intDivMacroKey = frontEnd.getNodeFactory().newAttribute(MacroConstants.NO_CHECK_DIVISION_BY_ZERO,
							Macro.class);

				root.setAttribute(intDivMacroKey, macroMap.get(MacroConstants.NO_CHECK_DIVISION_BY_ZERO));
				frontEnd.setIntDivAttributeKey(intDivMacroKey);
			}
		}
		return ast;
	}

	/**
	 * Translates a certain array of tokens into a list of AST's.
	 * 
	 * @param tokenSources
	 *            the array of tokens to be parsed.
	 * @return the list of AST's which is the result of parsing the token array.
	 * @throws SyntaxException
	 *             if there is a problem parsing the tokens.
	 * @throws ParseException
	 *             if there is a problem parsing the tokens.
	 */
	private List<AST> parseTokens(List<Pair<Language, CivlcTokenSource>> tokenSources)
			throws SyntaxException, ParseException {
		List<AST> asts = new ArrayList<>(tokenSources.size());

		for (Pair<Language, CivlcTokenSource> pair : tokenSources) {
			AST ast = parse(pair.left, pair.right);

			asts.add(ast);
		}
		return asts;
	}

	/**
	 * Preprocesses the files associated with this model translator into tokens.
	 * 
	 * @return the tokens which are the preprocessed result of the source files.
	 * @throws PreprocessorException
	 *             if there is any problem preprocessing the source files.
	 */
	private List<Pair<Language, CivlcTokenSource>> preprocess() throws PreprocessorException {
		List<Pair<Language, CivlcTokenSource>> tokenSources = new LinkedList<>();

		for (String filename : filenames) {
			File file = new File(filename);
			Language language = this.getLanguageByFileName(filename);
			Preprocessor preprocessor = frontEnd.getPreprocessor(language);
			CivlcTokenSource tokens = preprocessor.outputTokenSource(systemIncludes, userIncludes, macroMaps, file);

			// if(tokens instanceof PreprocessorTokenSource){
			// PreprocessorTokenSource pts = (PreprocessorTokenSource)tokens;
			// Map<String, Macro> macroMap = pts.getMacroMap();
			// System.out.println("+++++++++++++++++++++++");
			// Set<String> keys = macroMap.keySet();
			// for(String str : keys){
			// System.out.println("key:"+str);
			// }
			// }

			tokenSources.add(new Pair<>(language, tokens));
			if (config.showPreproc() || config.debugOrVerbose()) {
				out.println(bar + " Preprocessor output for " + filename + " " + bar);
				preprocessor.printOutputDebug(systemIncludes, userIncludes, macroMaps, out, file);
				out.println();
				out.flush();
			}
		}
		return tokenSources;
	}

	/**
	 * Translates command line marcos into ABC macro objects.
	 * 
	 * @param preprocessor
	 *            the preprocessor which would be used to translate macros.
	 * @return a map of macro keys and objects.
	 * @throws PreprocessorExceptions
	 *             if there is a problem preprocessing the macros.
	 */
	private Map<String, Macro> getMacroMaps(Language language) throws PreprocessorException {
		if (language.ordinal() == Language.FORTRAN77.ordinal())
			return new HashMap<String, Macro>();
		Map<String, Object> macroDefMap = cmdSection.getMapValue(macroO);
		Map<String, String> macroDefs = new HashMap<String, String>();
		Preprocessor preprocessor = frontEnd.getPreprocessor(language);

		if (this.cmdSection.isTrue(CIVLConstants.CIVLMacroO))
			macroDefs.put(CIVL_MACRO, "");
		if (this.cmdSection.isTrue(CIVLConstants.mpiContractO))
			macroDefs.put(MPI_CONTRACT_MACRO, "");
		if (macroDefMap != null) {
			for (String name : macroDefMap.keySet()) {
				macroDefs.put(name, (String) macroDefMap.get(name));
			}
		}
		return preprocessor.getMacros(macroDefs);
	}

	/**
	 * decides the language, either CIVL-C or Fortran, of a program by the
	 * suffix of the file name.
	 * 
	 * @param fileName
	 *            the file name of the program
	 * @return FORTRAN77 if the file name has suffix .f or .F, otherwise,
	 *         CIVL-C.
	 */
	private Language getLanguageByFileName(String fileName) {
		if (fileName.endsWith(".f") || fileName.endsWith(".F"))
			return Language.FORTRAN77;
		else
			return Language.CIVL_C;
	}

	/**
	 * Given a colon-separated list of filenames as a single string, this splits
	 * it up and returns an array of File objects, one for each name.
	 * 
	 * @param string
	 *            null or colon-separated list of filenames
	 * @return array of File
	 */
	private File[] extractPaths(String string) {
		if (string == null)
			return new File[0];
		else {
			String[] pieces = string.split(":");
			int numPieces = pieces.length;
			File[] result = new File[numPieces];

			for (int i = 0; i < numPieces; i++)
				result[i] = new File(pieces[i]);
			return result;
		}
	}

	/**
	 * Gets the user include paths, which are specified in the command line
	 * 
	 * @param section
	 *            the command line section this model translator corresponds to.
	 * @return the user include paths.
	 */
	private File[] getUserIncludes(GMCSection section) {
		return extractPaths((String) section.getValue(userIncludePathO));
	}

	/**
	 * This adds the default CIVL include path to the list of system includes.
	 *
	 * @param config
	 * @return list of system include directories specified in the (command
	 *         line) config object with the default CIVL include directory
	 *         tacked on at the end
	 */
	private File[] getSysIncludes(GMCSection config) {
		File[] sysIncludes = extractPaths((String) config.getValue(sysIncludePathO));
		int numIncludes = sysIncludes.length;
		File[] newSysIncludes = new File[numIncludes + 1];

		System.arraycopy(sysIncludes, 0, newSysIncludes, 0, numIncludes);
		newSysIncludes[numIncludes] = CIVLConstants.CIVL_INCLUDE_PATH;
		return newSysIncludes;
	}

	/**
	 * Finds all system libraries that are needed by the given AST, and compiles
	 * them into ASTs.
	 * 
	 * @param preprocessor
	 *            the preprocessor for preprocessing tokens.
	 * @param userAST
	 *            the AST of the input program, which is considered as the
	 *            "user" code, compared to libraries.
	 * @return The list of ASTs each of which corresponds to the implementation
	 *         of a library used by the input AST.
	 * @throws PreprocessorException
	 *             if there is a problem preprocessing the implementation file
	 *             of a library
	 * @throws SyntaxException
	 *             if there is a problem parsing the implementation file of a
	 *             library
	 * @throws ParseException
	 *             if there is a problem parsing the implementation file of a
	 *             library
	 * @throws IOException
	 *             if there is a problem reading the implementation file of a
	 *             library
	 */
	private List<AST> systemImplASTs(List<AST> userASTs)
			throws PreprocessorException, SyntaxException, ParseException, IOException {
		List<AST> result = new ArrayList<>();
		Set<String> processedSystemFilenames = new HashSet<>();
		Stack<AST> workList = new Stack<>();
		Preprocessor preprocessor = frontEnd.getPreprocessor(Language.CIVL_C);

		workList.addAll(userASTs);
		while (!workList.isEmpty()) {
			AST ast = workList.pop();

			for (SourceFile sourceFile : ast.getSourceFiles()) {
				String systemFilename = getSystemImplementationName(sourceFile.getFile());

				if (systemFilename != null && processedSystemFilenames.add(systemFilename)) {
					// the following ensures the file found will be
					// /include/civl/name.cvl, not something in the
					// current directory or elsewhere in the path.
					// It also ensures any file included will also
					// be found in either /include/civl or /include/abc.
					CivlcTokenSource tokens = preprocessor.outputTokenSource(civlSysPathArray, emptyFileArray,
							macroMaps, systemFilename, true);
					AST newAST = parse(Language.CIVL_C, tokens);

					workList.add(newAST);
					result.add(newAST);
				}
			}
		}
		return result;
	}

	/**
	 * Finds out the file name of the system implementation of a header file,
	 * which stands for a certain system library, such as civlc.cvh, mpi.h,
	 * omp.h, stdio.h, etc.
	 * 
	 * @param file
	 * @return The file name of the system implementation of the given header
	 *         file, or null if there is no implementation of the header file.
	 */
	private String getSystemImplementationName(File file) {
		String name = file.getName();

		if (CIVLConstants.getAllCivlLibs().contains(name))
			return name.substring(0, name.length() - 1) + "l";
		else if (CIVLConstants.getCinterfaces().contains(name))
			return name.substring(0, name.length() - 1) + "cvl";
		return null;
	}

}
