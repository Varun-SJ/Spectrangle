package model;


import java.util.HashMap;
import java.util.Map;

/**
 * RotatableTile is Tile that handles the rotation of a SimpleTile.
 * It utilizes a Map that stores the possible rotations of the SimpleTile it
 * represents. Methods on this class provide functionality to be used in the board and TUI.
 * @author Corjan van den Brink
 * @version 2019.01.24
 */
public class RotatableTile {
	
	private boolean upsideDown;
	private Rotation rotation;
	
	private Map<String, SimpleTile> tileVariants = new HashMap<>();
	
	/**
	 * Constructor for RotatableTile initiates a standard rotated tile and
	 * maps all variants. (Standard is !upsideDown and Rotation.R)
	 * @param right Color for right side
	 * @param other Color for other side
	 * @param left Color for left side
	 * @param points Point value of tile
	 */
	public RotatableTile(Color right, Color other, Color left, int points) {
		upsideDown = false;
		rotation = Rotation.R;
		
		// Map all (normal and Upside-down) rotated SimpleTiles using a string
		tileVariants.put("R", new SimpleTile(right, other, left, points));
		tileVariants.put("O", new SimpleTile(left, right, other, points));
		tileVariants.put("L", new SimpleTile(other, left, right, points));
		tileVariants.put("UR", new SimpleTile(right, left, other, points));
		tileVariants.put("UL", new SimpleTile(left, other, right, points));
		tileVariants.put("UO", new SimpleTile(other, right, left, points));
	}
	
	/**
	 * Creates RotatableTile by string Representation.
	 * @param strRep a valid string representation e.g. RGB4
	 * 		which contains 4 characters, three capitalized for color and one number for points
	 */
	public RotatableTile(String strRep) {
		this(Color.getByCharacter(strRep.charAt(0)), 
				Color.getByCharacter(strRep.charAt(1)), 
				Color.getByCharacter(strRep.charAt(2)),
				Integer.parseInt(strRep.substring(3, strRep.length())));
	}
	
	/*@
	 	ensures getRotation() == r;
	 */
	public void rotate(Rotation r) {
		rotation = r;
	}
	/*@
	 	ensures \old(isUpsideDown()) != isUpsideDown();
	 */
	public void flip() {
		upsideDown = !isUpsideDown();
	}
	
	/*@
	 	requires getVariants().values().contains(variant);
	 */
	/**
	 * Can be used to apply a SimpleTile variant to this RotatableTile.
	 * @param variant a valid variant for this RotatableTile
	 */
	public void applyVariant(SimpleTile variant) {
		for (String s: tileVariants.keySet()) {
			if (tileVariants.get(s).equals(variant)) {
				char rot;
				if (s.startsWith("U") && !isUpsideDown() || 
						!s.startsWith("U") && isUpsideDown()) {
					flip();
				}
				rot = s.charAt(s.length() - 1);
				switch (rot) {
					case 'R':
						rotate(Rotation.R);
						break;
					case 'L':
						rotate(Rotation.L);
						break;
					case 'O':
						rotate(Rotation.O);
						break;
				}
			}
		}
	}
	
	// ========= Getters ==========
	
	/*@ 
	 	ensures getVariants().keySet().contains(\result);
	 	pure
	 */
	/**
	 * Returns the String key that is used in the mapping according to the 
	 * fields rotation and upsideDown of the RotatableTile this is called on.
	 * @return key from {"R", "L", "O", "UR", "UL", "UO"}
	 */
	public String getVariantKey() {
		String key = "";
		if (isUpsideDown()) {
			key = "U";
		}
		key = key.concat(rotation.toString());
		return key;
	}
	
	/*@ 
	 	ensures getVariants().values().contains(\result);
	 	pure
	 */
	/**
	 * Getter for the variant of this Tile that conforms to the 
	 * current rotation and upsideDownness.
	 * @return the rotated variant in SimpleTile form
	 */
	public SimpleTile getVariant() {
		return tileVariants.get(getVariantKey());
	}
	
	/*@
	 	requires getVariants().keySet().contains(key);
	 	ensures \result.equals(getVariants().get(key));
	 	pure
	 */
	/**
	 * Gets variant based on valid key.
	 * @param key valid mapping key
	 * @return variant of this tile
	 */
	public SimpleTile getVariant(String key) {
		return tileVariants.get(key);
	}
	
	/**
	 * Gets all the variants.
	 * @return the variant mapping
	 */
	/*@	pure */	public Map<String, SimpleTile> getVariants() {
		return tileVariants;
	}
	
	/**
	 * Returns whether this tile has the variant.
	 * @param variant SimpleTile variant
	 * @return true if variant is in tileVariants
	 */
	public boolean hasVariant(SimpleTile variant) {
		return tileVariants.containsValue(variant);
	}
	
	/**
	 * Getter for upsideDown.
	 * @return upsideDown
	 */
	/*@	pure */	public boolean isUpsideDown() {
		return upsideDown;
	}

	/**
	 * Getter for rotation.
	 * @return rotation
	 */
	/*@	pure */	public Rotation getRotation() {
		return rotation;
	}
	
	/*@
	 	ensures \result == getVariant().getTilePoints();
	 	pure
	 */
	/**
	 * Returns the tilePoints for this tile.
	 * @return getVariant().getTilePoints()
	 */
	public int getTilePoints() {
		return getVariant().getTilePoints();
	}
	
	/**
	 * Calls the SimpleTile's generateTileString with the value for upsideDownness
	 * to display the RotatableTile correctly.
	 * @return string visualization of tile
	 */
	public String getTileString() {
		return getVariant().generateTileString(isUpsideDown());
	}
	
	
	/**
	 * Returns the initial encoding of the tile according to the protocol.
	 * @return String representation of tile (e.g. "PPG5")
	 */
	@Override
	public String toString() {
		return getVariant("R").getRightSide() + "" + 
				getVariant("R").getOtherSide() + "" + 
				getVariant("R").getLeftSide() + "" + 
				getVariant("R").getTilePoints() + "";
		
	}

	public static void main(String[] args) {
		/*
		 *  test for rotatable tiles, rotating them and printing them, inspecting
		 * 	shows correct behavior.
		 */
		
		RotatableTile tile1 = new RotatableTile(Color.B, Color.R, Color.P, 2);
		RotatableTile tile2 = new RotatableTile(Color.P, Color.P, Color.G, 5);
		
		System.out.println(tile1.toString());
		System.out.println(tile1.getTileString());
		tile1.rotate(Rotation.O);
		System.out.println(tile1.toString());
		System.out.println(tile1.getTileString());

		System.out.println(tile2.toString());
		System.out.print(tile2.getTileString());
		tile2.rotate(Rotation.L);
		System.out.println(tile2.toString());
		System.out.print(tile2.getTileString());
		tile2.flip();
		System.out.println(tile2.toString());
		System.out.println(tile2.getVariantKey());
		System.out.print(tile2.getTileString());
	}

}
