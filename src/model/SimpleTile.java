package model;


/**
 * Simple Tile saves information about the colors and the points of a tile
 * combined with the RotatableTile it achieves the full Tile functionality.
 * @author Corjan van den Brink
 * @version 2019.01.30
 */
public class SimpleTile {
	private Color right;
	private Color other;
	private Color left;
	private int points;
	
	public SimpleTile(Color right, Color other, Color left, int points) {
		this.right = right;
		this.other = other;
		this.left = left;
		this.points = points;
	}
	
	/**
	 * Gets right side.
	 * @return right side Color
	 */
	/*@ pure */ public Color getRightSide() {
		return this.right;
		
	}
	
	/**
	 * Gets other side.
	 * @return other side Color
	 */
	/*@ pure */ public Color getOtherSide() {
		return this.other;
	}

	/**
	 * Gets left side.
	 * @return left side Color
	 */
	/*@ pure */ public Color getLeftSide() {
		return this.left;
	}
	
	/**
	 * Gets tile points value.
	 * @return points
	 */
	/*@ pure */ public int getTilePoints() {
		return this.points;
	}
	
	/**
	 * Generates string visualization for this Tile variant.
	 * @param isUpsideDown for showing upsideDown tiles
	 * @return visualization for this tile
	 */
	/*@ pure */ public String generateTileString(boolean isUpsideDown) {
		String tileRepresentation;
		if (!isUpsideDown) {
			tileRepresentation = "\n" +
	                "                   ^\n" +
	                "                  / \\\n" +
	                "                 /" + getLeftSide() + " " + getRightSide() + "\\\n" +
	                "                /  " + getOtherSide() + "  \\\n" +
	                "               /=====" + getTilePoints() + "=\\\n";
		} else {
			tileRepresentation = "\n" +
	                "               \\=" + getTilePoints() + "=====/\n" +
	                "                \\  " + getOtherSide() + "  /\n" +
	                "                 \\" + getLeftSide() + " " + getRightSide() + "/\n" +
	                "                  \\ /\n" +
	                "                   v\n";

		}
		return tileRepresentation;
	}
	
}