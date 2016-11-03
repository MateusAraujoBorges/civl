package edu.udel.cis.vsl.civl.slice.common;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import edu.udel.cis.vsl.civl.kripke.IF.AtomicStep;
import edu.udel.cis.vsl.civl.kripke.IF.TraceStep;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.gmc.Trace;
import edu.udel.cis.vsl.gmc.TraceStepIF;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public class ErrorAutomaton {
	
	Set<CfaLoc> locs = new HashSet<>();
	Map<Location,CfaLoc> locToCfaLoc = new HashMap<>();
	
	Set<ErrorCfaLoc> locations;
	Set<CfaTransitionRelation> transitionRelations;
	ErrorCfaLoc initialLocation;
	ErrorCfaLoc errorLocation;
	List<ErrorCfaLoc> errorTrace;
	Map<SymbolicExpression,String> inputVariableSyntacticMap;
	Map<Integer,Integer> inputFrequencyMap;
	
	int theOnlyProcess = 0; /* We only work with single-threaded programs */
	boolean debug = false;
	
	public ErrorAutomaton (Model model, Trace<Transition, State> trace) {
		
		for (CIVLFunction f : model.functions()) {
			if (f.isSystemFunction() || f.toString().startsWith("__VERIFIER_")) continue;
			
			if (debug) System.out.println("  In function: "+f);
			for (Location l : f.locations()) {
				if (debug) System.out.println("    "+l+" has successors:");
				List<Statement> successors = new ArrayList<>();
				l.outgoing().forEach(successors::add);
				if (debug) for (Statement s : successors) System.out.println("      "+s);
			}
		}
		
		errorTrace = constructErrorTrace(trace);
		inputVariableSyntacticMap = makeSymbolicVariableMap(errorTrace);
		inputFrequencyMap = makeInputFrequencyMap(errorTrace);
		transitionRelations = transitionRelationsFromTrace(errorTrace);

		if (debug) {
			System.out.println("Error trace:");
			for (ErrorCfaLoc l : errorTrace) {
				if (!l.isExitLocation()) 
					System.out.println(l+" (Calling Context: "+l.callingContext+") "+"State:"+l.state.toString());
				else
					System.out.println("EXIT");
			}
		}
		
	}

	private Set<CfaTransitionRelation> transitionRelationsFromTrace(List<ErrorCfaLoc> errorTrace) {
		Set<CfaTransitionRelation> transitions = new HashSet<>();
		for (ErrorCfaLoc l : errorTrace) {
			if (l.isExitLocation()) break;
			
			ErrorCfaLoc source = l;
			CfaTransition transition = l.nextTransition();
			ErrorCfaLoc target = l.nextLocation();
			CfaTransitionRelation relation = new CfaTransitionRelation(source,transition,target);
			transitions.add(relation);
		}
		return transitions;
	}

	private Map<SymbolicExpression,String> makeSymbolicVariableMap(List<ErrorCfaLoc> errorTrace) {
		
		Map<SymbolicExpression,String> map = new HashMap<>();
		
		for (ErrorCfaLoc l : errorTrace) {
			if (l.isExitLocation()) break;
			
			Statement s = l.nextTransition().statement;
			if (s.toString().contains("__VERIFIER_nondet")) {
				LHSExpression lhs = ((CallOrSpawnStatement) s).lhs(); 
				Variable lhsVar = lhs.variableWritten();
				State postState = l.nextLocation().state;
				SymbolicExpression symExpr = postState.valueOf(theOnlyProcess, lhsVar);
				String variableName = lhsVar.name().toString();
				String line = getSourceLine(l.toString());
				map.put(symExpr, line+" "+variableName);
			}
		}
		System.out.println("\nBEGIN SymVar -> Line -> Var\n");
		System.out.println(printMap(map));
		System.out.println("END SymVar -> Line -> Var\n");
		return map;
	}
	
	private Map<Integer,Integer> makeInputFrequencyMap(List<ErrorCfaLoc> errorTrace) {
		
		Map<Integer,Integer> map = new HashMap<>();
		
		for (ErrorCfaLoc l : errorTrace) {
			if (l.isExitLocation()) break;
			
			Statement s = l.nextTransition().statement;
			if (s.toString().contains("__VERIFIER_nondet")) {
				
				String line = getSourceLine(l.toString());
				Integer lineNumber = Integer.valueOf(line);
				
				if (map.containsKey(lineNumber)) {
					map.put(lineNumber, map.get(lineNumber) + 1);
				} else {
					map.put(lineNumber, 1);
				}
			}
		}
		System.out.println("\nBEGIN Line -> Number of Input Reads\n");
		System.out.println(printMap(map));
		System.out.println("\nEND Line -> Number of Input Reads\n");
		return map;
	}
	
	private <K, V> String printMap (Map<K,V> map) {
        StringBuilder sb = new StringBuilder();
        for (K key : map.keySet()) sb.append("  "+key+" "+map.get(key)+"\n");
        return sb.toString();
	}

	
	private List<ErrorCfaLoc> constructErrorTrace (Trace<Transition, State> trace) {
		
		List<ErrorCfaLoc> errorTrace = new ArrayList<>();
		List<TraceStepIF<Transition, State>> steps = trace.traceSteps();
		Iterator<TraceStepIF<Transition, State>> it = steps.iterator();
		State preState = trace.init();
		
		/* Extract Location->Statement pairs from TraceStep Iterator */
		while(it.hasNext()) {
			TraceStep step = ((TraceStep) it.next());
			Iterable<AtomicStep> atomicSteps = step.getAtomicSteps();
			for(AtomicStep atom : atomicSteps){
				Location l = atom.getStatement().source();
				if (notFromOriginalSource(l)) {
					preState = atom.getPostState();
					continue;
				}
				
				Statement s = atom.getStatement();
				
				/* CfaLocation -> CfaTransition logic */
				ErrorCfaLoc loc = new ErrorCfaLoc(l, preState);
				CfaTransition tr = new CfaTransition(s);
				errorTrace.add(loc);
				loc.setNextTransition(tr);
				
				preState = atom.getPostState();
			}
		}
		
		/* Set Entry and Exit Locations */
		errorTrace.get(0).setEntryLocation();
		errorTrace.add(new ErrorCfaLoc()); // Internally sets a virtual exit
		
		doublyLinkErrorTrace(errorTrace);
		return errorTrace;
	}
	
	private void doublyLinkErrorTrace (List<ErrorCfaLoc> errorTrace) {
		for (int i = 0; i < errorTrace.size()-1; i++) {
			ErrorCfaLoc l = errorTrace.get(i);
			if (!l.isExitLocation()) {
				ErrorCfaLoc next = errorTrace.get(i+1);
				l.setNextLocation(next);
				l.successors.add(next);
			}
		}
	}
	
	private boolean notFromOriginalSource (Location l) {
		String fileName = l.getSource().getFileName();
		
		if (fileName.endsWith(".cvl") || 
				fileName.endsWith(".h") ||
				fileName.endsWith("Transformer")	) {
			return true;
		} else if (l.getNumOutgoing() == 1 &&
				l.getSoleOutgoing().toString().startsWith("$direct")) {
			return true;
		} else {
			return false;
		}
	}
	
	private String getSourceLine(String locationString) {
		
		Pattern p = Pattern.compile(":(\\d+)\\.");
		Matcher m = p.matcher(locationString);
		String line = "";
		if (m.find()) line = m.group(1);
		assert !line.isEmpty();
		
		return line;
	}
	
}
