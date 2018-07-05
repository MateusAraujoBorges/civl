package edu.udel.cis.vsl.civl.statistical;

import com.google.common.base.Preconditions;
import com.google.common.collect.Range;
import edu.udel.cis.vsl.gmc.util.BigRational;

public interface CountResult {

	CountResult multiply(BigRational val);

	CountResult multiply(CountResult count);

	CountResult plus(CountResult other);

	BigRational getMean();

	BigRational getVariance();

	default boolean isZero() {
		return getMean().isZero();
	}

	default Range<BigRational> getInterval(double delta) {
		BigRational mean = getMean();
		BigRational var = getVariance();

		Preconditions.checkState(mean.isPositive() || mean.isZero());
		Preconditions.checkState(var.isPositive() || var.isZero());

		if (var.isZero()) {
			return Range.closed(mean, mean);
		} else {
			double stdev = Math.sqrt(var.doubleValue());
			BigRational brDelta = BigRational.valueOf(delta);
			BigRational widthToCenter = BigRational.valueOf(stdev).mul(brDelta);
			BigRational lo = mean.sub(widthToCenter);
			if (lo.isNegative()) {
				lo = BigRational.ZERO;
			}
			BigRational hi = mean.add(widthToCenter);
			if (hi.compareTo(BigRational.ONE) > 0) {
				hi = BigRational.ONE;
			}
			return Range.closed(lo, hi);
		}
	}
}
