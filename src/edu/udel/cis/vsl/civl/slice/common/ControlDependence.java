package edu.udel.cis.vsl.civl.slice.common;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.util.IF.BranchConstraints;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;

public class ControlDependence {
	
	ErrorAutomaton trace;
	Map<CfaLoc,CfaLoc> ipdMap; /* One big map */
	Map<Location,CfaLoc> locToCfaLoc; /* One big map */
	Stack<ControlDependencyElement> cds;
	Set<BooleanExpression> slicedPC;
	File traceFile;
	boolean debug = false;
	
	public ControlDependence (ErrorAutomaton tr, Map<CfaLoc,CfaLoc> ipd,
			Map<Location,CfaLoc> locationMap, File f) {
		
		trace = tr;
		ipdMap = ipd;
		locToCfaLoc = locationMap;
		cds = new Stack<>();
		slicedPC = new HashSet<>();
		traceFile = f;
		
	}
	
	public Stack<ControlDependencyElement> collectControlDependencyStack () throws IOException {
		
		for (ErrorCfaLoc l : trace.errorTrace) {	
			if (isMerging(l)) mergingLogic(l);
			if (isBranching(l)) branchingLogic(l);
		}
		if (debug) {
			System.out.println("\nControl Dependence Stack:\n");
			for (ControlDependencyElement e : cds) {
				System.out.println(e);
				for (ErrorCfaLoc bp : e.branchPoints) {
					assert BranchConstraints.map != null : "BranchConstraints map is null";
					BooleanExpression symExpr = BranchConstraints.map.get(bp.state).left;
					String branchTaken = bp.nextTransition().statement.toString();
					System.out.println("   -> Conjunct from this region: "+symExpr+
							" (Branch taken: "+branchTaken+")");
				}
			}
		}
		
		System.out.println("\nBEGIN Guidance Lines\n");
		for (ControlDependencyElement e : cds) {
			for (ErrorCfaLoc bp : e.branchPoints) {
				System.out.println("  "+bp.sourceLine);
			}
		}
		System.out.println("\nEND Guidance Lines\n");
		
		System.out.println("\nBEGIN Control Dependent Slice\n");
		for (ControlDependencyElement e : cds) {
			for (ErrorCfaLoc bp : e.branchPoints) {
				assert BranchConstraints.map != null : "BranchConstraints map is null";
				Pair<BooleanExpression,BooleanExpression> symExprPair = BranchConstraints.map.get(bp.state);
				String branchTaken = bp.nextTransition().statement.toString();
				if (branchTaken.equals("TRUE_BRANCH_IF") || branchTaken.equals("LOOP_BODY_ENTER")) {
					slicedPC.add(symExprPair.left);
					System.out.println("  "+symExprPair.left);
				} else if (branchTaken.equals("FALSE_BRANCH_IF") || branchTaken.equals("LOOP_BODY_EXIT")) {
					slicedPC.add(symExprPair.right);
					System.out.println("  "+symExprPair.right);
				} else {
					assert false : "Branch taken is not binary, but: "+branchTaken;
				}
			}
		}
		System.out.println("\nEND Control Dependent Slice\n");
		System.out.println();
		
		outputSlicedPC(traceFile);
		
		return cds;
		
	}
	
	public Set<BooleanExpression> getSlicedPC() {
		return slicedPC;
	}
	
	/* This is setup to make the merging call as presented 
	 * in the 2007 paper */
	private void mergingLogic(ErrorCfaLoc l) {
		
		if (debug) System.out.println("Line "+l.sourceLine+" is a merge point");
		
		Location loc = l.getCIVLLocation();
		CfaLoc mergePoint = locToCfaLoc.get(loc);
		
		merging(mergePoint, l.callingContext);
		
	}
	
	/* This is setup to make the branching call as presented 
	 * in the 2007 paper */
	private void branchingLogic(ErrorCfaLoc branchPoint) {
		
		if (debug) System.out.println("Line "+branchPoint.sourceLine+" is a branch point");
		
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

		if (debug) System.out.println("Determining if "+l.nextTransition().statement
			+" (line "+l.sourceLine+") ("+l.getCIVLLocation().getSource().toString()+") is branching");
		if (l.isExitLocation()) {
			return false;
		} else {
		
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
	
	public void merging (CfaLoc mergePoint, int thisContext) {
		
		if (cds.isEmpty()) return;
		CfaLoc mergePointOnStack = cds.peek().mergePoint;
		int stackContext = cds.peek().context;
		
		if (mergePointOnStack.equals(mergePoint) &&
				(stackContext == thisContext)) {
			ControlDependencyElement c = cds.pop();
			if (debug) System.out.println("Just popped: "+c);
		}
		
	}

	public void branching (ErrorCfaLoc branchPoint, CfaLoc mergePoint, int thisContext) {
		
		if (!cds.isEmpty()) {
			CfaLoc mergePointOnStack = cds.peek().mergePoint;
			int stackContext = cds.peek().context;
			
			if (mergePointOnStack.equals(mergePoint) && 
					(stackContext == thisContext)) {
				if (debug) System.out.println("Branch points have the same merge point: "+mergePoint);
				if (debug) System.out.println("*** Adding branch point to CDS: "+branchPoint+" (line "+branchPoint.sourceLine);
				cds.peek().branchPoints.add(branchPoint);
			} else {
				ControlDependencyElement c = new ControlDependencyElement(branchPoint,
						mergePoint, thisContext);
				if (debug) System.out.println("Pushing "+c+" onto the stack");
				cds.push(c);
			}
		} else {
			ControlDependencyElement c = new ControlDependencyElement(branchPoint, mergePoint, thisContext);
			if (debug) System.out.println("Pushing "+c+" onto the stack");
			cds.push(c);
		}
		
	}

	private void outputSlicedPC(File traceFile) throws IOException {
		
		BufferedWriter output = null;
		String sliceFileName = traceFile.getAbsolutePath() + ".slice";
		try {
			File file = new File(sliceFileName);
            output = new BufferedWriter(new FileWriter(file));
            
			output.write(makeSliceString());
        } finally {
          if ( output != null ) {
            output.close();
          }
        }
	}
	
	private String makeSliceString() {
		String s = "";
		for (BooleanExpression e : slicedPC) s += e.toString().concat("\n");
		return s;
	}
}
