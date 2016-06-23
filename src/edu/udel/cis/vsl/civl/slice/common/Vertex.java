package edu.udel.cis.vsl.civl.slice.common;

import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.state.IF.State;

/**
 * Wrapper class for CIVL Locations.
 * 
 * @author mgerrard
 *
 */

public class Vertex {
	
	protected Location location;
	protected Set<Arc> in;
	protected Set<Arc> out;
	protected boolean onTracePath;
	
	protected State state;
	protected int pid;
	
	protected Vertex (Location l) {
		this.in = new HashSet<Arc>();
		this.out = new HashSet<Arc>();
		this.location = l;
	}
	
	public String toString() {
		if (this.location != null) {
			return this.location.toString()+" ("+this.hashCode()+")";
		} else {
			return "VIRTUAL EXIT";
		}
		
	}
	
	public String toTestString() {
		if (this.location != null) {
			return this.location.toString();
		} else {
			return "VIRTUAL EXIT";
		}
	}

}
