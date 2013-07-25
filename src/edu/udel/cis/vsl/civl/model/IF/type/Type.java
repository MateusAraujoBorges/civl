package edu.udel.cis.vsl.civl.model.IF.type;

/**
 * Parent of all types.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface Type {

	boolean isNumericType();

	boolean isIntegerType();

	boolean isRealType();

	boolean isPointerType();

}
