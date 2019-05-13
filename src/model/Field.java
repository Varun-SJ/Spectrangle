package model;

import java.util.List;

/**
 * Field class for building a board and holding a placed tile.
 * @author Varun Sudhakar
 * @author Corjan van den Brink
 * @version 2019.01.26
 */
public class Field {

	private int index;
	private int multiplier;
	private Field rightNeighbor, leftNeighbor, otherNeighbor;
	private RotatableTile tile;

	/**
	 * Creates this field at index with multiplier.
	 * @param index index of this field
	 * @param multiplier if field has bonus, multiplier is not 1, but 2, 3 or 4
	 */
	public Field(int index, int multiplier) {
		this.index = index;
		this.multiplier = multiplier;
		this.tile = null;
	}
	
	/**
	 * Getter for multiplier.
	 * @return multiplier multiplier of this field
	 */
	/*@ pure */	public int getMultiplier() {
		return this.multiplier;
	}
	
	/**
	 * Getter for index.
	 * @return index
	 */
	/*@ pure */	public int getIndex() {
		return this.index;
	}
	
	/**
	 * Getter for tile.
	 * @return tile
	 */
	/*@ pure */ public RotatableTile getTile() {
		return this.tile;
		
	}
	
	/**
	 * Puts tile at this field.
	 * @param newTile to be placed tile
	 */
	//@ ensures getTile().equals(newTile);
	public void putTile(RotatableTile newTile) {
		this.tile = newTile;
	}
	
	/**
	 * Returns if has tile.
	 * @return true if tile is not null
	 */
	/*@ pure */	public boolean hasTile() {
		return tile != null;
	}
	
	/**
	 * Returns if is bonus.
	 * @return true if multiplier bigger than 1
	 */
	/*@ pure */	public boolean isBonus() {
		return getMultiplier() > 1;
	}
	
	public boolean isUpsideDown() {
		List<Integer> coord = Board.index2Coord(getIndex());
		return (coord.get(0) + coord.get(1)) % 2 == 1;
	}
	
	/**
	 * Returns if Field is neighbor to a field with a tile on it, and is empty and therefore is a 
	 * valid choice for tile placement.
	 * @return true if neighboring
	 */
	/*@ pure */ public boolean isNeighbor() {
		boolean hasNeighborWithTile = false;
		if (hasLeftNeighbor() && getLeftNeighbor().hasTile()) {
			hasNeighborWithTile = true;
		}
		if (hasRightNeighbor() && getRightNeighbor().hasTile()) {
			hasNeighborWithTile = true;
		}
		if (hasOtherNeighbor() && getOtherNeighbor().hasTile()) {
			hasNeighborWithTile = true;
		}
		return !hasTile() && hasNeighborWithTile;
	}
	
	/*
	 * Getters, setters and checkers for every neighbor.
	 */
	
	//@ ensures getRightNeighbor().equals(right);
	public void setRightNeighbor(Field right) {
		this.rightNeighbor = right;
	}
	
	/*@ pure */ public Field getRightNeighbor() {
		return rightNeighbor;
	}
	
	/*@ pure */ public boolean hasRightNeighbor() {
		return getRightNeighbor() != null;
	}
	
	//@ ensures getLeftNeighbor().equals(left);
	public void setLeftNeighbor(Field left) {
		this.leftNeighbor = left;
	}
	
	/*@ pure */ public Field getLeftNeighbor() {
		return leftNeighbor;
	}
	
	/*@ pure */ public boolean hasLeftNeighbor() {
		return getLeftNeighbor() != null;
	}
	
	//@ ensures getOtherNeighbor().equals(other);
	public void setOtherNeighbor(Field other) {
		this.otherNeighbor = other;
	}
	
	/*@ pure */ public Field getOtherNeighbor() {
		return otherNeighbor;
	}
	
	/*@ pure */ public boolean hasOtherNeighbor() {
		return getOtherNeighbor() != null;
	}
	
}
