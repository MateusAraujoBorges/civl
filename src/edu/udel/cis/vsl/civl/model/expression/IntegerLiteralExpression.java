/**
 * 
 */
package edu.udel.cis.vsl.civl.model.expression;

import java.math.BigInteger;

/**
 * An integer literal.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class IntegerLiteralExpression extends LiteralExpression {

	private BigInteger value;

	/**
	 * An integer literal.
	 * 
	 * @param value
	 *            The (arbitrary precision) value of the integer.
	 */
	public IntegerLiteralExpression(BigInteger value) {
		this.value = value;
	}

	/**
	 * @return The (arbitrary precision) value of the integer.
	 */
	public BigInteger value() {
		return value;
	}

	/**
	 * @param value
	 *            The (arbitrary precision) value of the integer.
	 */
	public void setValue(BigInteger value) {
		this.value = value;
	}
	
	@Override
	public String toString() {
		return value.toString();
	}

}
