package edu.udel.cis.vsl.civl.slice.common;

import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.state.IF.State;

/**
 * Wrapper class for CIVL Traces.
 * 
 * @author mgerrard
 *
 */

public class SliceTrace {
	public Location location;
	public Statement statement;
	public State state;
	public int pid;
}
