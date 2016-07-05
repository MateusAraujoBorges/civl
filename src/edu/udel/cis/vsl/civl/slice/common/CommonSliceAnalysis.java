package edu.udel.cis.vsl.civl.slice.common;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import edu.udel.cis.vsl.civl.kripke.IF.AtomicStep;
import edu.udel.cis.vsl.civl.kripke.IF.TraceStep;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.expression.AbstractFunctionCallExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.AddressOfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ArrayLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BooleanLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BoundVariableExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.CastExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.CharLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DereferenceExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DerivativeCallExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DomainGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DotExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DynamicTypeOfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionIdentifierExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.HereOrRootExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.InitialValueExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.IntegerLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.MemoryUnitExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ProcnullExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RealLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RecDomainLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.RegularRangeExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ScopeofExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SelfExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SizeofTypeExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.StructOrUnionLiteralExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SubscriptExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SystemGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UndefinedProcessExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.NoopStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.ReturnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement.StatementKind;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.model.common.statement.CommonCallStatement;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.slice.IF.DominatorAnalysis;
import edu.udel.cis.vsl.civl.slice.IF.SliceAnalysis;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.gmc.Trace;
import edu.udel.cis.vsl.gmc.TraceStepIF;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * This analysis is based on the ideas found in Xin and 
 * Zhang's 2007 paper: 
 *   "Efficient Online Detection of 
 *     Dynamic Control Dependence"
 * 
 * The analysis walks backwards along an error trace to 
 * determine the input variables and branches taken
 * during execution which are relevant to reaching the
 * error.
 * 
 * The analysis first constructs a Control Flow Automata
 * (the dual of a CFG), which is just a wrapper over the
 * Statements and Locations of CIVL's labeled transition
 * system.
 * 
 * We then compute the immediate static post-dominators
 * of each node (Location):
 * 
 * A node d post-dominates a node n if every path from
 * the exit node to n must go through d. A node d strictly 
 * post-dominates a node n if d post-dominates n and d does 
 * not equal n. The immediate post-dominator of a node n is 
 * the post-dominator of n that doesn't strictly post-dominate 
 * any other strict post-dominators of n.
 * 
 * We use the immediate post-dominator map to run a
 * Control Dependence Analysis as in the 2007 paper.
 * 
 * @author mgerrard
 *
 */

public class CommonSliceAnalysis implements SliceAnalysis {
	
	Set<Vertex> reachableUpToMerge;
	FlowGraph controlFlowGraph;
	private boolean someReachableNodeIsSuspicious;
	private Map<Vertex, Set<Variable>> mergePointVariables;
	private Set<Vertex> IPDset;
	//input variable and declaration line number 
	public Set<Pair<SymbolicExpression,String>> inputSymbolicExprs;
	public Map<String,String> symbolicToSyntactic;
	// [input variables, branches involved, branches-in-question]
	public List<Set<String>> expectedOutput = Arrays.asList(new HashSet<String>(),new HashSet<String>(),new HashSet<String>());
	
	/* SETUP */
	List<String> inputInstances = new ArrayList<String>();
	/* We will populate this list with the corresponding vertices in the trace */
	List<Vertex> forwardTrace = new ArrayList<Vertex>();
	/* Mark source locations of statements with a function call */
	Set<Location> visited = new HashSet<Location>(); 
	/* Keep track of respective positions in both the trace and the ICFG */
	Pair<Location,Vertex> positionInTraceAndGraph = new Pair<Location,Vertex>(null,null);
	
	List<SliceTrace> traceStepLocStmt;
	FlowGraph ICFG;
	Vertex virtualExit;
	Map<Vertex,Vertex> IPDmap = new HashMap<Vertex,Vertex>();
	
	public CommonSliceAnalysis (Model model, Trace<Transition, State> trace, File traceFile) throws IOException {		
		model.print(System.out, false);
		createICFG(model,trace);
		discoverPostdominators();
		runControlDependenceAnalysis();
		outputAnalysisResults(traceFile);
		printAssumptions(model, trace);
	}

	private void createICFG(Model model, Trace<Transition, State> trace) throws IOException {
		createTraceStructure(trace);
		initializeFlowGraph(model);
		syncTraceWithICFG();
		inlineFunctionsIntoICFG();
		addVirtualExit();
		printGraph(ICFG);
		this.controlFlowGraph = ICFG;
		writeDotFile();
	}

	private void outputAnalysisResults(File traceFile) throws IOException {
		Set<String> inputVars = this.expectedOutput.get(0);
		System.out.println("INPUT VARIABLES: \n  "+inputVars);
		Set<String> errorBranches = this.expectedOutput.get(1);
		System.out.println("ERROR BRANCHES: \n  "+errorBranches);
		Set<String> questions = this.expectedOutput.get(2);
		System.out.println("QUESTIONABLE BRANCHES: \n  "+questions);
		BufferedWriter output = null;
		String sliceFileName = traceFile.getAbsolutePath() + ".slice";
		try {
            File file = new File(sliceFileName);
            output = new BufferedWriter(new FileWriter(file));
            output.write("INPUT VARIABLES:\n");
            for (String s : inputVars) output.write("  "+s+"\n");
            output.write("ERROR BRANCHES:\n");
            for (String s : errorBranches) output.write("  "+s+"\n"); 
            output.write("QUESTIONABLE BRANCHES:\n");
            for (String s : questions) output.write("  "+s+"\n");
        } catch ( IOException e ) {
            e.printStackTrace();
        } finally {
          if ( output != null ) {
            output.close();
          }
        }
	}

	private void runControlDependenceAnalysis() {
		System.out.println("\n************ CONTROL DEPENDENCE ANALYSIS ******************\n");
		Stack<Pair<Vertex,Vertex>> CDS = new Stack<Pair<Vertex,Vertex>>();
		List<Stack<Pair<Vertex,Vertex>>> traceOfCDS = collectCDSTrace(CDS);
		List<Pair<Vertex,Arc>> tracePairs = createTracePairs();
		
		/* Reverse lists before feeding them into analyzer */
		List<Vertex> backwardTrace = forwardTrace; Collections.reverse(backwardTrace);
		List<Stack<Pair<Vertex,Vertex>>> backwardTraceOfCDS = traceOfCDS; Collections.reverse(backwardTraceOfCDS);
		List<Pair<Vertex,Arc>> backwardTracePairs = tracePairs; Collections.reverse(backwardTracePairs);
		/* Make sure lists start with the branch preceding the error (assuming branch is next to error) */
		int indexOfBranchPrecedingError = findIndexOfErrorVertex(backwardTrace) + 1;
		backwardTrace = backwardTrace.subList(indexOfBranchPrecedingError,backwardTrace.size());
		backwardTraceOfCDS = backwardTraceOfCDS.subList(indexOfBranchPrecedingError,backwardTraceOfCDS.size());
		/* Minus 2 because we didn't include the last two nodes in this trace */
		backwardTracePairs = backwardTracePairs.subList(indexOfBranchPrecedingError-2, backwardTracePairs.size());
		@SuppressWarnings("unused")
		Pair<Set<Vertex>,Set<Vertex>> errorBranchesAndQuestionables = findErrorBranchesAndQuestionables(backwardTracePairs, backwardTraceOfCDS);
	}

	private List<Pair<Vertex, Arc>> createTracePairs() {
		/* This will be our <Vertex,Arc> trace data structure */
		List<Pair<Vertex,Arc>> tracePairs = new ArrayList<Pair<Vertex,Arc>>();
		/* Stop at size()-2 iterations because we don't want to include the NULL exit node */
		for (int j = 0; j < forwardTrace.size()-2; j++) {
			Vertex v1 = forwardTrace.get(j);
			Vertex v2 = forwardTrace.get(j+1);
			assert (v1 != null && v2 != null);
			Arc a = findConnectingArc(v1,v2);
			assert a != null : "Arc "+v1+" can't find the arc to it's neighboring bud "+v2;
			tracePairs.add(new Pair<Vertex,Arc>(v1,a));
		}
		System.out.println("The <Vertex,Arc> trace pairs are:"+tracePairs);
		return tracePairs;
	}

	@SuppressWarnings("unchecked")
	private List<Stack<Pair<Vertex, Vertex>>> collectCDSTrace(
			Stack<Pair<Vertex, Vertex>> CDS) {
		List<Stack<Pair<Vertex,Vertex>>> traceOfCDS = new ArrayList<Stack<Pair<Vertex,Vertex>>>();
		for (Vertex v : forwardTrace) {
			if (isImmediatePostdominator(v)) {
				if (!CDS.empty()) {
					CDS = merging(v,CDS);
				}
			}
			if (isBranchPoint(v)) {
				CDS = branching(v,IPDmap.get(v),CDS);
			}
			System.out.println("The Control Dependence Stack after looking at "+v+" is: \n  "+CDS);
			traceOfCDS.add((Stack<Pair<Vertex,Vertex>>) CDS.clone());
		}
		System.out.println("CDS trace:");
		for (Stack<Pair<Vertex,Vertex>> cds : traceOfCDS) System.out.println(cds);
		return traceOfCDS;
	}

	private void discoverPostdominators() {
		/* Discover the postdominators using the ICFG */
		Map<Vertex,Set<Vertex>> ICFGmap = new HashMap<Vertex,Set<Vertex>>();
		for (Vertex v : ICFG.vertices) {
			Set<Vertex> targets = new HashSet<Vertex>();
			for (Arc a : v.out) {
				targets.add(a.target);
			}
			ICFGmap.put(v, targets);
		}
		/* We pass in the successor (not pred) map and the exit (not entry) node to compute the dual (postdominator) analysis */
		DominatorAnalysis<Vertex> postDom = new CommonDominatorAnalysis<Vertex>(ICFG.vertices, ICFGmap, virtualExit);
		Map<Vertex,Set<Vertex>> postDominatorMap = postDom.computeDominators();	
		/* Discover the IPD by walking forward through the dynamic trace with postdominator map in hand */
		
		for (int j = 0; j < forwardTrace.size()-1; j++) {
			if (!IPDmap.containsKey(forwardTrace.get(j))) {
				IPDmap = findIPD(forwardTrace, j, postDominatorMap, IPDmap);
			}
		}
		
		Collection<Vertex> IPDcollection = IPDmap.values();
		this.IPDset = new HashSet<Vertex>(IPDcollection);
	}

	private void writeDotFile() throws IOException {
		String dotStr = toDotFileString(ICFG);
		try(  PrintWriter outGraph = new PrintWriter( "/Users/mgerrard/Desktop/graph.dot" )  ){
		    outGraph.println( dotStr );
		}
		
		Runtime rt = Runtime.getRuntime();
		rt.exec("/opt/local/bin/dot -Tpng -o /Users/mgerrard/Desktop/graph.png /Users/mgerrard/Desktop/graph.dot");
	}

	/* There is no location for the program exit, so let's create a virtual exit node */
	private void addVirtualExit() {
		this.virtualExit = new Vertex(null);
		ICFG.vertices.add(virtualExit);
		forwardTrace.add(virtualExit);
		for (Arc a : ICFG.arcs) {
			if (a.target == null) {
				System.out.println("Pointing "+a+", which has a source of "+a.source+" to virtual exit");
				a.target = virtualExit;
			}
		}
	}

	private void inlineFunctionsIntoICFG() {
		int i = 0;
		/* Step through the trace, inlining CFGs of encountered statements into the ICFG */
		for (SliceTrace step : traceStepLocStmt) {
			assert (positionInTraceAndGraph.left.equals(positionInTraceAndGraph.right.location)) : "Positions not synced: "+
					positionInTraceAndGraph.left+" does not equal "+positionInTraceAndGraph.right.location;
			Location loc = step.location; Statement stmt = step.statement;
			if (isFunctionCall(stmt,visited) && isNotCIVLprimitive(stmt)) {
				FlowGraph g = processFunctionStatement(stmt);
				ICFG = spliceLocalGraphIntoICFG(positionInTraceAndGraph.right.out, ICFG, g);
				/* Mark this call location so we don't remake a CFG if it is revisited */
				visited.add(loc); 
			}
			syncTraceLocWithICFG(stmt, i);
			i++;
		}
	}

	private void syncTraceLocWithICFG(Statement stmt, int i) {
		/* Sync trace location with ICFG vertex */
		if (traceStepLocStmt.size() > (i+1)) {
			Location nextLocation = traceStepLocStmt.get(i+1).location;
			positionInTraceAndGraph.left = nextLocation;
			Vertex currentVertex = positionInTraceAndGraph.right;
			Vertex nextVertex = findTargetVertex(stmt, currentVertex);
			nextVertex.onTracePath = true;
			forwardTrace.add(nextVertex);
			positionInTraceAndGraph.right = nextVertex;
			System.out.println("______ The position pair after syncing: "+positionInTraceAndGraph);
			/* Put some State into the Vertex */
			currentVertex.state = traceStepLocStmt.get(i).state;
			currentVertex.pid = traceStepLocStmt.get(i).pid;
		}
	}

	private FlowGraph processFunctionStatement(Statement stmt) {
		CallOrSpawnStatement callStmt = (CallOrSpawnStatement) stmt;
		CIVLFunction f = callStmt.function();
		Map<Variable,Set<Variable>> formalToActualMap = associateFormalToActual(f,callStmt);
		/* Create function CFG */
		FlowGraph g = new FlowGraph(f,formalToActualMap);
		assert g.entryVertex != null : "The local graph's entry vertex is null";
		return g;
	}

	/* Sync positions of first location in the trace and initial ICFG entry */
	private void syncTraceWithICFG() {
		positionInTraceAndGraph.left = traceStepLocStmt.get(0).location;
		positionInTraceAndGraph.right = ICFG.entryVertex;
		forwardTrace.add(ICFG.entryVertex);
	}

	private void initializeFlowGraph(Model model) {
		this.ICFG = new FlowGraph(model.rootFunction(),null);
		/* Keep track of which vertices are in the trace for coloring the output graph */
		ICFG.entryVertex.onTracePath = true;
	}

	private void createTraceStructure(Trace<Transition, State> trace) {
		List<TraceStepIF<Transition, State>> steps = trace.traceSteps();
		Iterator<TraceStepIF<Transition, State>> it = steps.iterator();
		this.traceStepLocStmt = traceLocStmtPairs(it);
	}

	private boolean isNotCIVLprimitive(Statement stmt) {
		return (!stmt.toString().startsWith("$assume") &&
				!stmt.toString().startsWith("$havoc")  &&
				!stmt.toString().startsWith("$assert"));
	}

	private Arc findConnectingArc (Vertex v1, Vertex v2) {
		Arc arc = null;
		for (Arc a : v1.out) if (v2.in.contains(a)) arc = a;
		assert arc != null : "Vertex "+v1+" with out set "+v1.out+"\ncouldn't find the relation arc to vertex "+v2+" with in set "+v2.in;
		return arc;
	}
	
	private Pair<Set<Vertex>,Set<Vertex>> findErrorBranchesAndQuestionables (
			List<Pair<Vertex,Arc>> trace, List<Stack<Pair<Vertex,Vertex>>> traceOfCDS) {
		this.inputSymbolicExprs = new HashSet<Pair<SymbolicExpression,String>>();
		this.symbolicToSyntactic = new HashMap<String,String>();
		this.mergePointVariables = new HashMap<Vertex,Set<Variable>>();
		Set<Vertex> branchesInQuestion = new HashSet<Vertex>();
		
		/* Assume there is some control dependency when the error is hit */
		assert !traceOfCDS.get(0).empty() : "The error has no control dependencies";
		Expression cond = extractAssertionCondition(traceOfCDS);
		Set<Variable> variables = collectVariablesInAssertion(cond);
		Set<Vertex> branches = new HashSet<Vertex>();
		branches.addAll(collectBranchesOfInterest(traceOfCDS.get(0)));
		System.out.println("***Branches of interest after processing the error CDS:");
		for (Vertex n : branches) System.out.println("  "+n);	
		/* Here we want to create a global director of the statements
		 * which aren't nested inside a conditional. This is to handle
		 * the case when the stack is empty.
		 */
		Vertex globalEntry = new Vertex(null);
		/* Add it to the list of branches (it serves as the TOP value)*/
		branches.add(globalEntry);
		
		/* Advance past error node */
		trace = trace.subList(1, trace.size()); traceOfCDS = traceOfCDS.subList(1, traceOfCDS.size()); 
		
		slice(trace, traceOfCDS, branches, globalEntry, cond, variables, branchesInQuestion);
		
		if (!branches.isEmpty()) {
			System.out.println("**The error branches are**");
			for (Vertex b : branches) {
				System.out.println("  "+b);
			}
		} else {
			System.out.println("** There are NO error branches!**");
		}
		/* Expected output for unit testing */
		Set<String> errorBranches = new HashSet<String>();
		for (Vertex b : branches) {
			if (b.location != null) errorBranches.add(b.toTestString());
		}
		this.expectedOutput.set(1, errorBranches);
		System.out.println(this.expectedOutput);
		
		if (!branchesInQuestion.isEmpty()) {
			System.out.println("**The branches in QUESTION are**");
			for (Vertex b : branchesInQuestion) {
				System.out.println("  "+b);
			}
		} else {
			System.out.println("** There are NO branches in question!**");
		}
		Set<String> questionables = new HashSet<String>();
		for (Vertex b : branchesInQuestion) {
			questionables.add(b.toTestString());
		}
		this.expectedOutput.set(2, questionables);
		
		Pair<Set<Vertex>,Set<Vertex>> errorBranchesAndQuestionables = 
				new Pair<Set<Vertex>,Set<Vertex>>(branches, branchesInQuestion);
		Set<String> inputVars = new HashSet<String>();
		for (Pair<SymbolicExpression,String> v : this.inputSymbolicExprs) {
			inputVars.add("("+v.left.toString()+","+v.right.trim()+")");
		}
		this.expectedOutput.set(0, inputVars);
		return errorBranchesAndQuestionables;
	}
	
	private void slice(List<Pair<Vertex, Arc>> trace, 
			List<Stack<Pair<Vertex, Vertex>>> traceOfCDS, Set<Vertex> branches, 
			Vertex globalEntry, Expression cond, Set<Variable> variables, 
			Set<Vertex> branchesInQuestion) {
		Map<Arc,VariableState> funcReturnToLHSVarMap = createFunctionCallAssignmentMap(trace);
		int i = 0;
		for (Pair<Vertex,Arc> elem : trace) {			
			/* First discover the branch upon which this
			 * statement immediately control depends
			 */
			Vertex currentDirectingBranch;
			Stack<Pair<Vertex,Vertex>> currentCDS = traceOfCDS.get(i);
			if (!currentCDS.empty()) {
				currentDirectingBranch = traceOfCDS.get(i).peek().left;
			} else {
				/* If the CDS is empty, the current director
				 * is the "true" global entry point 
				 */
				currentDirectingBranch = globalEntry;
			}
			/* Here we're looking for either assign statements, 
			 * branch points, or merge points;
			 * we don't care about the other statements
			 */
			if (isBranchPoint(elem.left)) {
				System.out.println("Found a branch point: "+elem);
				System.out.println("Let's collect any variables involved");
				Vertex currentBranch = elem.left;
				System.out.println("***The branch on top of the CDS: "+currentBranch);
				cond = getConditionalExpression(currentBranch);
				System.out.println("***The condition in this branch, whose vars we'll collect: "+cond);
				variables.addAll(collectVariables(cond));
				if (!branches.contains(currentBranch)) {
					System.out.println("++ NOW collecting branches of interest");
					branches.addAll(collectBranchesOfInterest(traceOfCDS.get(i)));
					/* Run a DFS on subgraph of branch, up to the merge point of this region */
					if (offBranchContainsNodeOfInterest(currentBranch, currentCDS.peek().right)) {
						branchesInQuestion.add(currentBranch);
					}
				}
			} else if (isImmediatePostdominator(elem.left) || (isAssign(elem.right, funcReturnToLHSVarMap))) {
				if (isImmediatePostdominator(elem.left)) {
					System.out.println("Found an immediate postdominator (merge point): "+elem);
					this.mergePointVariables.put(elem.left, variables);
				}
				String statementString = elem.right.statement.toString();
				if (isAssign(elem.right, funcReturnToLHSVarMap)) {
					Variable lhsVar = null;
					if (elem.right.statement instanceof AssignStatement) {
						AssignStatement assign = (AssignStatement) elem.right.statement;
						lhsVar = assign.getLhs().variableWritten();
						System.out.println("Found an ASSIGN STMT, whose LHS variable is: "+lhsVar);
						if (variables.contains(lhsVar)) {
							System.out.println("The LHS of "+elem.right+" contains a variable of interest");
							System.out.println("Let's remove the LHS variable from our variables worklist");
							
							variables.remove(lhsVar);
							System.out.println("And add all variables (if any) on the RHS");
							Expression rhs = assign.rhs();
							variables.addAll(collectVariables(rhs));
							if (!branches.contains(currentDirectingBranch)) {
								branches.addAll(collectBranchesOfInterest(currentCDS));
								System.out.println("** Found some NEW branches of interest:");
								for (Vertex b : branches) {
									System.out.println("   "+b);
								}
							}
						}
					} else {
						/* The assign is from a returned function call */
						lhsVar = funcReturnToLHSVarMap.get(elem.right).variable;
						System.out.println("Found an ASSIGN CALL, whose LHS variable is: "+lhsVar);
						System.out.println("The element here is: "+elem);
						if (variables.contains(lhsVar)) {
							System.out.println("The LHS of "+elem.right+" contains a variable of interest");
							if (statementString.contains("__VERIFIER_nondet_int")) {
								int successiveLine = Integer.parseInt(elem.right.target.location.getSource().toString().replaceAll(".*:([0-9]+)..*", "$1"));
								String inputVarLine = String.valueOf(successiveLine - 1);
								inputInstances.add(inputVarLine);
								System.out.println("LHS var: "+lhsVar.name());
								//this.inputVariables.add(lhsVar);
								VariableState vs = funcReturnToLHSVarMap.get(elem.right);
								State state = vs.state; 
								int pid = vs.pid;
								state.print(System.out);
								
								System.out.println("The RHS target state: "+state);
								SymbolicExpression s = state.valueOf(pid, vs.variable); //'input' Variable not in scope
								System.out.println("State: "+state);
								System.out.println("Symbolic Expression: "+s);
								this.inputSymbolicExprs.add(new Pair<SymbolicExpression,String>(s,inputVarLine+" "+lhsVar.name()+" "));
								this.symbolicToSyntactic.put(s.toString(), inputVarLine);
							}
							System.out.println("Let's remove the LHS variable from our variables worklist");
							variables.remove(lhsVar);
							
							/* TODO : is this correct?? */
							System.out.println("And add all variables on the RHS or vars passed into the function call (if any)");
							Expression rhs = ((ReturnStatement) elem.right.statement).expression();
							System.out.println("The expression on the RHS of the function call: "+rhs);
							variables.addAll(collectVariables(rhs));
						}

//							/* Also check out any variables passed as arguments into the function */
//							variables.addAll(collectVariables(rhs));
//							for (Expression e : assignFromCall.arguments()) {
//								variables.addAll(collectVariables(e));
//							}
//							if (!branches.contains(currentDirectingBranch)) {
//								branches.addAll(collectBranchesOfInterest(currentCDS));
//								System.out.println("** Found some NEW branches of interest:");
//								for (Vertex b : branches) {
//									System.out.println("   "+b);
//								}
//							}
//						}
					}
					
				}
				System.out.println("\nCurrent variables of interest:\n"+variables+"\n");
			} else {
				System.out.println("Node "+elem+" is not an assign, branch, or a merge, "+
									"so we'll ignore it");
				System.out.println("  The statement kind of the Arc is: "+elem.right.statement.statementKind());
			}
			i++;
		}
	}

	private Expression extractAssertionCondition(
			List<Stack<Pair<Vertex, Vertex>>> traceOfCDS) {
		Vertex branchClosestToError = traceOfCDS.get(0).peek().left;
		Expression cond = getConditionalExpression(branchClosestToError);
		return cond;
	}

	private Set<Variable> collectVariablesInAssertion(Expression cond) {
		Set<Variable> variables = new HashSet<Variable>();
		variables.addAll(collectVariables(cond));
		System.out.println("***Variables in conditional closest to error:");
		for (Variable v : variables) {
			System.out.println("  "+v);
		}
		return variables;
	}

	private boolean offBranchContainsNodeOfInterest(Vertex currentBranch,
			Vertex mergePoint) {
		this.reachableUpToMerge = new HashSet<Vertex>();
		this.someReachableNodeIsSuspicious = false;
		inspectBranchSubgraph(currentBranch, mergePoint, this.reachableUpToMerge);
		if (this.someReachableNodeIsSuspicious) {
			return true;
		} else {
			return false;
		}
	}

	private void inspectBranchSubgraph(Vertex currentBranch, Vertex mergePoint,
			Set<Vertex> reachable) {
		reachable.add(currentBranch);
		if (currentBranch.equals(mergePoint)) {
			return;
		} else if (isSuspicious(currentBranch, mergePoint)) {
			this.someReachableNodeIsSuspicious = true;
			return;
		}
		/*
		 * TODO: remove null pointers
		for (Vertex s : controlFlowGraph.succMap.get(currentBranch)) {
			if (!reachable.contains(s)) {
				inspectBranchSubgraph(s, mergePoint, reachable);
			}
		}
		*/
	}

	@SuppressWarnings("unused")
	private boolean isSuspicious(Vertex v, Vertex mergePoint) {
		for (Arc a : v.out){ 
			if (isUnstructuredControlFlow(a)) {
				return true;
			} else if (isAssign(a)){
				AssignStatement assign = (AssignStatement) a.statement;
				Variable lhsVar = assign.getLhs().variableWritten();
				assert lhsVar != null;
				Expression rhs = assign.rhs();
				/* mergePointVariables is a map containing all relevant variables
				 * collected up to the given merge point */
				assert this.mergePointVariables != null;
				assert mergePoint != null;
				if (!this.mergePointVariables.isEmpty() && 
						!this.mergePointVariables.get(mergePoint).isEmpty() &&
						this.mergePointVariables.get(mergePoint).contains(lhsVar)) {
					return true;
				} else if (lhsVar.hasPointerRef()) {
					return true;
				} else if (lhsVar.type() instanceof CIVLArrayType) {
					return true;
				} else {
					return false;
				}	
			} else if (isFunctionCall(a)){
				System.out.println("We've hit some function call");
				return true;
			} 
		}
		return false;
	}
	
	private boolean isUnstructuredControlFlow(Arc a) {
		Statement s = a.statement;
		if (s != null && (isReturnStmt(s) || isGotoStmt(s))) {
			return true;
		} else {
			return false;
		}
	}
	
	private boolean isAssign(Arc a) {
		if (a.statement != null) {
			return (a.statement.statementKind() == StatementKind.ASSIGN);
		} else {
			return false;
		}
	}
	
	private boolean isReturnStmt (Statement s) {
		return s.statementKind() == Statement.StatementKind.RETURN;
	}
	
	private boolean isGotoStmt (Statement s) {
		return (s.statementKind() == Statement.StatementKind.NOOP &&
				((NoopStatement) s).noopKind() == NoopStatement.NoopKind.GOTO);
	}
	
	private boolean isFunctionCall(Arc a) {
		return (a.statement != null && a.statement instanceof CommonCallStatement);
	}

	private Map<Arc,VariableState> createFunctionCallAssignmentMap (List<Pair<Vertex,Arc>> trace) {
		Map<Arc,VariableState> exprVarMap = new HashMap<Arc,VariableState>();
		
		/* Stack that will track returned Expressions */
		Stack<Arc> returnedExprs = new Stack<Arc>();
		
		for (Pair<Vertex,Arc> elem : trace) {
			/* If you see a RETURN Statement with a non-null Expression, 
			 * push the Expression onto the stack */
			if (elem.right.statement.statementKind() == Statement.StatementKind.RETURN &&
					((ReturnStatement) elem.right.statement).expression() != null) {
				returnedExprs.add(elem.right);
			}
			/* If you see a CallOrSpawnStatement with an LHS,
			 * get the returned Expression from the stack */
			if (elem.right.statement.statementKind() == Statement.StatementKind.CALL_OR_SPAWN &&
					((CallOrSpawnStatement) elem.right.statement).lhs() != null) {
				Expression lhs = ((CallOrSpawnStatement) elem.right.statement).lhs();
				/* Get the Variable in the singleton set returned from calling collectVariables(lhs) */
				Variable lhsVar = collectVariables(lhs).stream().findAny().get();
				Arc a = returnedExprs.pop();
				assert a != null;
				VariableState vs = new VariableState();
				vs.variable = lhsVar; vs.pid = elem.left.pid;
				/* Take the state from the arc's source, because the state
				 * needs to be in scope of the returned variable  */
				vs.state = a.source.state;
				exprVarMap.put(a, vs);
			}
		}
		return exprVarMap;
	}
	
	private Set<Vertex> collectBranchesOfInterest (Stack<Pair<Vertex,Vertex>> CDS) {
		Set<Vertex> branches = new HashSet<Vertex>();
		for (Pair<Vertex,Vertex> region : CDS) {
			/* The left element is the director of the region */
			branches.add(region.left); 
		}
		return branches;
	}
	
	private Expression getConditionalExpression(Vertex v) {
		Expression cond = null;
		for (Arc a : v.out) { cond = a.statement.guard(); break; }
		return cond;
	}

	private int findIndexOfErrorVertex (List<Vertex> trace) {
		for (Vertex v : trace) {
			for (Arc a : v.out) {
				if (a.toString().equals("__VERIFIER_error()")) return trace.indexOf(v);
			}
		}
		/* Assume an error vertex exists */
		assert false; return -1;
	}
	
	private <E> Stack<Pair<E,E>> branching (E branch, E branchIPD,
			Stack<Pair<E,E>> CDS) {
		/* The third boolean expression is my addition to the 
		 * algorithm: because we add virtual merge nodes which
		 * do not necessarily map to unique branch points, we also
		 * check if the branch points are the same
		 */
		if (!CDS.empty() && CDS.peek().right.equals(branchIPD) &&
				CDS.peek().left.equals(branch)) {
			CDS.peek().left = branch;
		} else {
			CDS.push(new Pair<E,E>(branch,branchIPD));
		}
		return CDS;
	}
	
	private <E> Stack<Pair<E,E>> merging (E mergePoint, Stack<Pair<E,E>> CDS) {
		if (!CDS.empty() && CDS.peek().right.equals(mergePoint)) {
			CDS.pop();
		}
		return CDS;
	}
	
	private boolean isBranchPoint (Vertex v) {
		return v.out.size() > 1;
	}
	
	private boolean isImmediatePostdominator (Vertex v) {
		return this.IPDset.contains(v);
	}
	
	private boolean isAssign(Arc a, Map<Arc, VariableState> funcReturnToLHSVarMap) {
		if (a.statement != null) {
			if (a.statement.statementKind() == StatementKind.ASSIGN) {
				return true;
			}
			if (funcReturnToLHSVarMap.get(a) != null) {
				return true;
			} else {
				return false;
			}
		} else {
			return false;
		}
	}
	
	private <E> Map<E,E> findIPD (List<E> trace, int index, 
			Map<E,Set<E>> postDoms, Map<E,E> IPD) {
		int succIndex = index + 1;
		int traceSize = trace.size();
		E thisNode = trace.get(index);
		
		Set<E> domSet = postDoms.get(thisNode);
		if (domSet != null) {
			for (int i = succIndex; i < traceSize; i++) {
				E s = trace.get(i);
				if (domSet.contains(s)) {
					IPD.put(thisNode, s);
					break;
				}
			}
		}
		return IPD;
	}

	private Map<Variable, Set<Variable>> associateFormalToActual(
			CIVLFunction f, CallOrSpawnStatement callStmt) {
		Map<Variable,Set<Variable>> map = new HashMap<Variable,Set<Variable>>();
		List<Variable> formalParams = f.parameters();
		List<Expression> arguments = callStmt.arguments();
		for (int i=0; i<formalParams.size(); i++) {
			Variable param = formalParams.get(i);
			Expression actualArg = arguments.get(i);
			Set<Variable> varsInArg = collectVariables(actualArg);
			map.put(param, varsInArg);
		}
		return map;
	}

	private FlowGraph spliceLocalGraphIntoICFG(Set<Arc> preds, FlowGraph ICFG, FlowGraph localGraph) {
		assert localGraph.entryVertex != null : "The local graph's entry vertex is null";
		/* Add all vertices and arcs from the local graph to the ICFG */
		ICFG.vertices.addAll(localGraph.vertices);
		ICFG.arcs.addAll(localGraph.arcs);
		/* There should only be one arc for any given function call statement */
		assert(preds.size() == 1);
		Vertex originalSuccVertex = null;
		for (Arc p : preds) {
			if (p.originalTarget == null) {
				p.originalTarget = p.target;
				originalSuccVertex = p.target;
			} else {
				originalSuccVertex = p.originalTarget;
			}			p.target = localGraph.entryVertex; 
			localGraph.entryVertex.in.add(p);
		}
		for (Arc exit : localGraph.exitArcs) {
			exit.target = originalSuccVertex;
			originalSuccVertex.in.add(exit);
		}
		return ICFG;
	}

	private Vertex findTargetVertex(Statement stmt, Vertex currentVertex) {
		for (Arc a : currentVertex.out) {
			if (a.statement.equals(stmt)) {
				assert a.target != null : "This arc has no target: "+a+" \n   but its equivalent statement has target: "+stmt.target();
				return a.target;
			}
		}
		assert(false) : "We did not find the Target Vertex in the ICFG";
		return null;
	}

	private void printGraph(FlowGraph g) {
		System.out.println("***** FLOW GRAPH *****\n");
		for (Vertex v : g.vertices) {
			System.out.println("  Vertex: "+v);
			System.out.println("    -> IN : "+v.in);
			System.out.println("    -> OUT:"+v.out);
		}
		System.out.println("\n**********************\n");
	}

	private boolean isFunctionCall(Statement stmt, Set<Location> visited) {
		return (stmt instanceof CallOrSpawnStatement);
		/* The following allows 'toy1*.c' to process */
		//return (stmt instanceof CallOrSpawnStatement && !visited.contains(stmt.source()));
	}

	public String toDotFileString(FlowGraph g) {
		String fileStr = "digraph {\n";
		for (Vertex v : g.vertices) {
			for (Arc a : v.out) {
				/* Sanitize string for dot file */
				String arcStr = a.toString().replaceAll("\"","'");
				String directedEdge = "\""+v+"\" -> \""+a.target+"\" [label=\"  "+arcStr+"\"]\n";
				fileStr = fileStr + directedEdge;
			}
		}
		/* Color the vertices on the trace path */
		for (Vertex v : g.vertices) {
			if (v.onTracePath) {
				String vertexColoring = "\""+v+"\" [color=red]\n";
				fileStr = fileStr + vertexColoring;
			}
		}
		fileStr = fileStr + "}";
		return fileStr;
	}
	
	/* Extract Location-Statement pairs from TraceStep Iterator */
	private List<SliceTrace> traceLocStmtPairs(
			Iterator<TraceStepIF<Transition, State>> it) {
		List<Pair<Location, Statement>> tracePairs = new ArrayList<Pair<Location, Statement>>();
		List<SliceTrace> sliceTrace = new ArrayList<SliceTrace>();
		while(it.hasNext()) {
			TraceStep step = ((TraceStep) it.next());
			Iterable<AtomicStep> atomicSteps = step.getAtomicSteps();
			for(AtomicStep atom : atomicSteps){
				Location l = atom.getStatement().source();
				Statement s = atom.getStatement();
				tracePairs.add(new Pair<Location,Statement>(l,s));
				SliceTrace t = new SliceTrace();
				t.location = l;
				t.statement = s;
				//t.state = step.getFinalState();
				t.state = atom.getPostState();
				System.out.println("Post state: "+t.state);
				t.state.print(System.out);
				
				t.pid = step.processIdentifier();
				System.out.println("The state for "+t.statement+" is: "+t.state);
				sliceTrace.add(t);
			}
		}
		return sliceTrace;
	}
	
	/* Collect Variables from a given Expression */
	private Set<Variable> collectVariables(Expression expr) {
		Set<Variable> vars = new HashSet<Variable>();
		collectVariablesWorker(expr,vars);
		return vars;
	}
	
	private void collectVariablesWorker(Expression expr, Set<Variable> vars) {
		if (expr instanceof AbstractFunctionCallExpression) {
			List<Expression> args = ((AbstractFunctionCallExpression) expr).arguments();
			for (Expression e : args) 
				collectVariablesWorker(e,vars);
		} else if (expr instanceof AddressOfExpression) {
			collectVariablesWorker(((AddressOfExpression)expr).operand(),vars);
		} else if (expr instanceof ArrayLiteralExpression) {
			Expression[] elements = ((ArrayLiteralExpression) expr).elements();
			for (Expression e : elements)
				collectVariablesWorker(e,vars);
		} else if (expr instanceof BinaryExpression) {
			Expression left = ((BinaryExpression) expr).left();
			Expression right = ((BinaryExpression) expr).right();
			collectVariablesWorker(left,vars);
			collectVariablesWorker(right,vars);
		} else if (expr instanceof BooleanLiteralExpression) {
			// do nothing - is this correct?
		} else if (expr instanceof BoundVariableExpression) {
			// ask 
		} else if (expr instanceof CastExpression) {
			Expression e = ((CastExpression) expr).getExpression();
			collectVariablesWorker(e,vars);
		} else if (expr instanceof CharLiteralExpression) {
			// do nothing
		} else if (expr instanceof ConditionalExpression) {
			// ask 
			ConditionalExpression condExpr = (ConditionalExpression) expr;
			Expression cond = condExpr.getCondition();
			Expression trueBranch = condExpr.getTrueBranch();
			Expression falseBranch = condExpr.getFalseBranch();
			collectVariablesWorker(cond,vars);
			collectVariablesWorker(trueBranch,vars);
			collectVariablesWorker(falseBranch,vars);
		} else if (expr instanceof DereferenceExpression) {
			Expression p = ((DereferenceExpression) expr).pointer();
			collectVariablesWorker(p,vars);
		} else if (expr instanceof DerivativeCallExpression) {
			// what are these expressions?
			List<Pair<Variable, IntegerLiteralExpression>> partials = ((DerivativeCallExpression) expr).partials();
			for (Pair<Variable, IntegerLiteralExpression> p : partials) {
				vars.add(p.left);
			}
		} else if (expr instanceof DomainGuardExpression) {
			// ask what this is doing
		} else if (expr instanceof DotExpression) {
			// ask  
			Expression e = ((DotExpression) expr).structOrUnion();
			collectVariablesWorker(e,vars);
		} else if (expr instanceof DynamicTypeOfExpression) {
			// do nothing
		} else if (expr instanceof FunctionGuardExpression) {
			// ask 
			FunctionGuardExpression fgExpr = (FunctionGuardExpression) expr;
			Expression funcExpr = fgExpr.functionExpression();
			collectVariablesWorker(funcExpr,vars);
			List<Expression> args = fgExpr.arguments();
			for (Expression e : args) {
				collectVariablesWorker(e,vars);
			}
		} else if (expr instanceof FunctionIdentifierExpression) {
			// do nothing
		} else if (expr instanceof HereOrRootExpression) {
			// do nothing
		} else if (expr instanceof InitialValueExpression) {
			Variable v = ((InitialValueExpression) expr).variable();
			vars.add(v);
		} else if (expr instanceof IntegerLiteralExpression) {
			// do nothing
		} else if (expr instanceof LHSExpression) {
			Variable v = ((LHSExpression) expr).variableWritten();
			vars.add(v);
		} else if (expr instanceof LiteralExpression) {
			// do nothing
		} else if (expr instanceof MemoryUnitExpression) {
			Variable v = ((MemoryUnitExpression) expr).variable();
			vars.add(v);
		} else if (expr instanceof ProcnullExpression) {
			// do nothing (this is just an empty interface extending Expression)
		} else if (expr instanceof QuantifiedExpression) {
			// is this correct?
			Expression e = ((QuantifiedExpression) expr).expression();
			collectVariablesWorker(e,vars);
		} else if (expr instanceof RealLiteralExpression) {
			// do nothing
		} else if (expr instanceof RecDomainLiteralExpression) {
			// ask 
		} else if (expr instanceof RegularRangeExpression) {
			// this is a CIVL-C expression kind - can we ignore?
		} else if (expr instanceof ScopeofExpression) {
			LHSExpression lhsExpr = ((ScopeofExpression) expr).argument();
			Expression e = (Expression) lhsExpr;
			collectVariablesWorker(e,vars);
		} else if (expr instanceof SelfExpression) {
			// do nothing
		} else if (expr instanceof SizeofExpression) {
			Expression e = ((SizeofExpression) expr).getArgument();
			collectVariablesWorker(e,vars);
		} else if (expr instanceof SizeofTypeExpression) {
			// do nothing
		} else if (expr instanceof StructOrUnionLiteralExpression) {
			// do nothing
		} else if (expr instanceof SubscriptExpression) {
			// ask 
		}  else if (expr instanceof SystemGuardExpression) {
			List<Expression> args = ((SystemGuardExpression) expr).arguments();
			for (Expression e : args) {
				collectVariablesWorker(e,vars);
			}
		} else if (expr instanceof UnaryExpression) {
			Expression e = ((UnaryExpression) expr).operand();
			collectVariablesWorker(e,vars);
		} else if (expr instanceof UndefinedProcessExpression) {
			// do nothing	
		} else if (expr instanceof VariableExpression) {
			vars.add(((VariableExpression)expr).variable());
		} else {
			assert false;
		}
	}
	
	private BooleanExpression getFinalPC (Model model, Trace<Transition, State> trace) {
		/* Hack to access PC just before final state */
		List<TraceStepIF<Transition,State>> traceSteps = trace.traceSteps();
		State secondToLastState = traceSteps.get(traceSteps.size()-2).getFinalState();
		BooleanExpression pathCondition = secondToLastState.getPathCondition();
		return pathCondition;
	}
	
	private void printAssumptions (Model model, Trace<Transition, State> trace) {
		BooleanExpression pathCondition = getFinalPC(model, trace);
		BooleanExpression[] pcClauses = pathCondition.getClauses();
		Set<BooleanExpression> slice = new HashSet<BooleanExpression>();
		Set<String> lineAndAssumption = new HashSet<String>();
		for (BooleanExpression c : pcClauses) {
			for (Pair<SymbolicExpression,String> s : this.inputSymbolicExprs) {
				if (c.toString().contains(s.left.toString())) {
					slice.add(c);
					lineAndAssumption.add(s.right+" "+c.toString());
				}
			}
		}
		System.out.println("Clauses in slice:");
		for (BooleanExpression c : slice) {
			System.out.println("  "+c);
		}
		System.out.println("BEGIN ASSUMPTIONS");
		for (String s : lineAndAssumption) {
			System.out.println(s);
		}
		System.out.println("END ASSUMPTIONS");
		System.out.println("BEGIN INPUT");
		for(String input : inputInstances) {
			System.out.println(input);
		}
		System.out.println("END INPUT");
		System.out.println("BEGIN MAP");
		for(String k : symbolicToSyntactic.keySet()) {
			System.out.println(k+" "+symbolicToSyntactic.get(k));
		}
		System.out.println("END MAP");
		System.out.println("Size of slice: "+slice.size());
		System.out.println("Size of PC   : "+pcClauses.length);
		/* Reasoner reasoner = modelTranslator.universe.reasoner(pathCondition);
		String pcString = replayer.symbolicAnalyzer.pathconditionToString(source,
				secondToLastState, "  ", reasoner.getReducedContext()).toString();
		System.out.println("\nPath Condition:"+pcString); */
	}

	@Override
	public Set<Pair<SymbolicExpression, String>> inputSymbolicExprs() {
		return this.inputSymbolicExprs;
	}

	public Map<String, String> symbolicToSyntactic() {
		return this.symbolicToSyntactic;
	}

	@Override
	public List<Set<String>> expectedOutput() {
		return this.expectedOutput;
	}
}

