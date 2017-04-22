package edu.udel.cis.vsl.civl.util.IF;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

public class CartesianProductSolver<T> implements Iterable<List<T>> {
	private List<List<T>> results;

	public CartesianProductSolver(List<List<T>> args) {
		int numSets = args.size();

		if (numSets <= 0)
			results = new LinkedList<>();
		else {
			results = new LinkedList<>();

			results.add(new LinkedList<>());
			for (List<T> vector : args)
				results = vectorSetProd(vector, results);
		}
	}

	/**
	 * The cartesian product of a vector T[] v AND a set of vectors
	 * List-of-List-of-T s:
	 */
	private List<List<T>> vectorSetProd(List<T> vector, List<List<T>> set) {
		List<List<T>> newSet = new LinkedList<>();

		for (List<T> vec : set) {
			for (T e : vector) {
				List<T> newVec = new LinkedList<>(vec);

				newVec.add(e);
				newSet.add(newVec);
			}
		}
		return newSet;
	}

	@Override
	public Iterator<List<T>> iterator() {
		return results.iterator();
	}
}
