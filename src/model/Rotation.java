package model;

import java.util.ArrayList;
import java.util.List;

/**
 * Rotation based on the protocol.
 * Rotations are the side of the triangle from which the tilestring is read clockwise.
 * Example tile RGB4 with rotation L (not upside-down) is a 4 value tile with sides:
 * 		left: R, right:G, other:B
 * @author Corjan van den Brink
 * @version 2019.01.26
 */
public enum Rotation {
	R, // default, start reading from right side
	L,
	O;
	
	/**
	 * Returns all rotations as strings.
	 * @return rotations as list of strings
	 */
	public static List<String> getRotations() {
		List<String> rotations = new ArrayList<>();
		rotations.add(R.toString());
		rotations.add(L.toString());
		rotations.add(O.toString());
		return rotations;
	}
}
