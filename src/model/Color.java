package model;


/**
 * Enumeration of the colors a tile's sides can have.
 * @author Varun Sudhakar
 * @author Corjan van den Brink
 * @version 2019.01.26 
 */
public enum Color {
	
	R, // Red
	G, // Green
	B, // Blue
	Y, // Yellow
	P, // Purple
	W; // White
	
	/**
	 * Checks whether a color is valid next to another color.
	 * White is valid next to all colors. 
	 * @param adjColor to check with respect to.
	 * @return true if this and adjacent color are equals or one of them is white
	 */
	/*@ pure */ public boolean isValidAdjacent(Color adjColor) {
		return this == adjColor || this == W || adjColor == W;
	}
	
	/**
	 * Converts a valid character to a Color.
	 * @param colorChar capitalized character {R, G, B, P, Y, W}
	 * @return color
	 */
	public static Color getByCharacter(char colorChar) {
		switch (colorChar) {
			case 'R':
				return R;
			case 'G':
				return G;
			case 'B':
				return B;
			case 'Y':
				return Y;
			case 'P':
				return P;
			case 'W':
				return W;
			default:
				return null;
		}
	}

}
