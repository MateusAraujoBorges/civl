package edu.udel.cis.vsl.civl.statistical;

import com.google.common.base.Preconditions;
import edu.udel.cis.vsl.gmc.util.BigRational;

public class StatisticalCountResult implements CountResult {

	public static final StatisticalCountResult ZERO = new StatisticalCountResult(BigRational.ZERO);

	private final BigRational mean;
	private final BigRational variance;

	public StatisticalCountResult(BigRational mean, BigRational variance) {
		Preconditions.checkArgument(!variance.isNegative());
		Preconditions.checkArgument(!mean.isNegative());

		this.mean = mean;
		this.variance = variance;
	}

	public StatisticalCountResult(BigRational val) {
		Preconditions.checkArgument(!val.isNegative());
		this.mean = val;
		this.variance = BigRational.ZERO;
	}

	@Override
	public StatisticalCountResult multiply(BigRational val) {
		return new StatisticalCountResult(mean.mul(val), variance.mul(val).mul(val));
	}

	@Override
	public StatisticalCountResult multiply(CountResult count) {
		// qcoral approach
		if (this.variance.isPositive() || count.getVariance().isPositive()) {
			BigRational ex = this.getMean();
			BigRational ey = count.getMean();
			BigRational vx = this.getVariance();
			BigRational vy = count.getVariance();

			BigRational exy = ex.mul(ey);
			BigRational vxy = ex.pow(2).mul(vy).add(ey.pow(2).mul(vx)).add(vx.mul(vy));
			// can't find a way to take the square root of a BigRational

			return new StatisticalCountResult(exy, vxy);
		} else {
			return new StatisticalCountResult(this.getMean().mul(
							count.getMean()), BigRational.ZERO);
		}
	}

	@Override
	public StatisticalCountResult plus(CountResult other) {
		return new StatisticalCountResult(
						this.getMean().add(other.getMean()),
						this.getVariance().add(other.getVariance()));
	}

	@Override
	public BigRational getMean() {
		return mean;
	}

	@Override
	public BigRational getVariance() {
		return variance;
	}

	@Override
	public String toString() {
		return "StatisticalCountResult [mean="
						+ mean + ", variance=" + variance + "]";
	}
}
