package edu.udel.cis.vsl.civl.slice.common;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintStream;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.util.IF.BranchConstraints;
import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;

public class ControlDependence {
	
	ErrorAutomaton trace;
	Map<CfaLoc,CfaLoc> ipdMap; /* One big map */
	Map<Location,CfaLoc> locToCfaLoc; /* One big map */
	Stack<ControlDependencyElement> cds;
	Set<BooleanExpression> slicedPC;
	Set<BooleanExpression> minimizedSlice;
	File traceFile;
	boolean debug = false;
	
	/** Stdout: where most output is going to go, including error reports */
	private PrintStream out = System.out;
	
	public ControlDependence (ErrorAutomaton tr, Map<CfaLoc,CfaLoc> ipd,
			Map<Location,CfaLoc> locationMap, File f) {
		
		trace = tr;
		ipdMap = ipd;
		locToCfaLoc = locationMap;
		cds = new Stack<>();
		slicedPC = new HashSet<>();
		minimizedSlice = new HashSet<>();
		traceFile = f;
		
	}
	
	public Stack<ControlDependencyElement> collectControlDependencyStack () throws IOException {
		
		for (ErrorCfaLoc l : trace.errorTrace) {	
			if (isMerging(l)) mergingLogic(l);
			if (isBranching(l)) branchingLogic(l);
		}
		if (debug) {
			out.println("\nControl Dependence Stack:\n");
			for (ControlDependencyElement e : cds) {
				out.println(e);
				for (ErrorCfaLoc bp : e.branchPoints) {
					BooleanExpression symExpr = bp.branchConstraint;
					String branchTaken = bp.nextTransition().statement.toString();
					out.println("   -> Conjunct from this region: "+symExpr+
							" (Branch taken: "+branchTaken+")");
				}
			}
		}
		
		out.println("\nBEGIN Guidance Lines\n");
		assert !cds.isEmpty() : "The Control Dependency Stack is empty.";
		for (ControlDependencyElement e : cds) {
			if (debug) out.println("CDS element: "+e);
			for (ErrorCfaLoc bp : e.branchPoints) {
				out.println("  "+bp.sourceLine);
			}
		}
		out.println("\nEND Guidance Lines\n");
		
		assert BranchConstraints.evaluator != null : "BranchConstraints has no evaluator";
		for (ControlDependencyElement e : cds) {
			for (ErrorCfaLoc bp : e.branchPoints) {
				assert bp.branchConstraint != null : "This branch point has no associated branch constraint.";
				slicedPC.add(bp.branchConstraint);
			}
		}
		
		minimizedSlice = makeMinimizedPC(slicedPC);
		
		out.println("\nBEGIN Control Dependent Slice\n");
		for (BooleanExpression e : minimizedSlice) {
			out.println("  "+e);
		}
		out.println("\nEND Control Dependent Slice\n");
		
		outputSlicedPC(traceFile);
		
		return cds;
		
	}
	
	public Set<BooleanExpression> getSlicedPC() {
		return slicedPC;
	}
	
	/* This is setup to make the merging call as presented 
	 * in the 2007 paper */
	private void mergingLogic(ErrorCfaLoc l) {
		
		if (debug) out.println("Line "+l.sourceLine+" is a merge point");
		
		Location loc = l.getCIVLLocation();
		CfaLoc mergePoint = locToCfaLoc.get(loc);
		
		merging(mergePoint, l.callingContext);
		
	}
	
	/* This is setup to make the branching call as presented 
	 * in the 2007 paper */
	private void branchingLogic(ErrorCfaLoc branchPoint) {
		
		if (debug) out.println("Line "+branchPoint.sourceLine+" is a branch point");
		
		Location branchLoc = branchPoint.getCIVLLocation();
		CfaLoc branch = locToCfaLoc.get(branchLoc);
		CfaLoc mergePoint = ipdMap.get(branch);
		assert mergePoint != null : branchPoint.getCIVLLocation()+"'s merge point is null";
		
		branching(branchPoint, mergePoint, branchPoint.callingContext);
		
	}

	private boolean isMerging(ErrorCfaLoc l) {
		
		if (l.isExitLocation()) {
			return false;
		} else {
			Location loc = l.getCIVLLocation();
			CfaLoc cfaLoc = locToCfaLoc.get(loc);
			
			return cfaLoc.isIPD;
		}
	}
	
	private boolean isBranching(ErrorCfaLoc l) {

		if (l.isExitLocation()) {
			return false;
		} else {
			//if (debug) out.println("Determining if "+l.nextTransition().statement
				//	+" (line "+l.sourceLine+") ("+l.getCIVLLocation().getSource().toString()+") is branching");
		
			Location loc = l.getCIVLLocation();
			CfaLoc cfaLoc = locToCfaLoc.get(loc);
			
			if (cfaLoc.isBranching) {
				String guardString = cfaLoc.location.getOutgoing(0).guard().toString(); 
				if (guardString.startsWith("$sef$")) {
					return false; // This is an instrumented branch directive
				} else {
					return true;
				}
			} else {
				return false;
			}
		}
	}
	
	public void merging (CfaLoc mergePoint, int callingContext) {
		
		if (cds.isEmpty()) return;
		CfaLoc mergePointOnStack = cds.peek().mergePoint;
		int stackContext = cds.peek().context;
		
		if (mergePointOnStack.equals(mergePoint) &&
				(stackContext == callingContext)) {
			ControlDependencyElement c = cds.pop();
			if (debug) out.println("\n--- Just popped: "+c+"\n");
		}
		
	}

	public void branching (ErrorCfaLoc branchPoint, CfaLoc mergePoint, int callingContext) {
		
		if (!cds.isEmpty()) {
			CfaLoc mergePointOnStack = cds.peek().mergePoint;
			int stackContext = cds.peek().context;
			
			if (mergePointOnStack.equals(mergePoint) && 
					(stackContext == callingContext)) {
				if (debug) out.println("Branch points have the same merge point: "+mergePoint);
				if (debug) out.println("\n+++ Pushing "+branchPoint+" (line "+
						branchPoint.sourceLine+") onto the stack. Context: "+callingContext+"\n");
				cds.peek().branchPoints.add(branchPoint);
			} else {
				ControlDependencyElement c = new ControlDependencyElement(branchPoint,
						mergePoint, callingContext);
				if (debug) out.println("\n+++ Pushing "+c+" onto the stack. Context: "+c.context+"\n");
				cds.push(c);
			}
		} else {
			ControlDependencyElement c = new ControlDependencyElement(branchPoint, mergePoint, callingContext);
			if (debug) out.println("\n+++ Pushing "+c+" onto the stack");
			cds.push(c);
		}
		
		
	}

	private void outputSlicedPC(File traceFile) throws IOException {
		
		BufferedWriter output = null;
		String sliceFileName = traceFile.getAbsolutePath() + ".slice";
		try {
			File file = new File(sliceFileName);
            output = new BufferedWriter(new FileWriter(file));
            
			output.write(sliceStrings());
        } finally {
          if ( output != null ) {
            output.close();
          }
        }
	}
	
	private Set<BooleanExpression> makeMinimizedPC(Set<BooleanExpression> clauses) {
		Set<BooleanExpression> impliedClauses = new HashSet<BooleanExpression>();
		
		SymbolicUniverse universe = SARL.newStandardUniverse();
			
		BooleanExpression context = universe.trueExpression();
		Reasoner reasoner = universe.reasoner(context);
						
		for (BooleanExpression c : clauses) {
			BooleanExpression antecedent = universe.trueExpression();
			for (BooleanExpression other : clauses) {
				if (other.equals(c)) continue;
				antecedent = universe.and(antecedent, other);
			}
			
			BooleanExpression implication = universe.implies(antecedent, c);
			
			if (reasoner.isValid(implication)) {
				impliedClauses.add(c);
			}
		}
		
		Set<BooleanExpression> minimizedClauses = new HashSet<BooleanExpression>();
		minimizedClauses.addAll(clauses);
		minimizedClauses.removeAll(impliedClauses);
		
		return minimizedClauses;
	}

	private String sliceStrings () {
		
		String s = "";
		s += "*** Original PC ***\n";
		for (BooleanExpression c : slicedPC) s += "   "+c+"\n";
		
		s += "*** Minimized PC ***\n";
		for (BooleanExpression c : minimizedSlice) s += "   "+c+"\n";
		
		return s;
	}
}
