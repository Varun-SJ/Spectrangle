package model;


import java.util.ArrayList;
import java.util.List;

import controller.InvalidIndexException;

/**
 * Class for board of Spectrangle game.
 * @author Varun Sudhakar
 * @author Corjan van den Brink
 * @version 2019.01.29
 */
public class Board {

	public static final int BOARD_SIZE = 36;
	private boolean emptyBoard;
	public List<Field> fields = new ArrayList<>();

	/**
	 * Creates board with empty Fields and bonuses assigned to the correct fields.
	 */
	public Board() {
		
		/**
		 * Setting the indices of the bonus spaces. 
		 * Implemented in this manner since the
		 * bonus spaces do not change.
		 */

		int multiplier;
		for (int x = 0; x < BOARD_SIZE; x++) {
			multiplier = 1;

			if (x == 10 || x == 14 || x == 30) {
				multiplier = 2;
			} else if (x == 2 || x == 26 || x == 34) {
				multiplier = 3;
			} else if (x == 11 || x == 13 || x == 20) {
				multiplier = 4;
			}

			fields.add(new Field(x, multiplier));
		}
		linkFields();
		emptyBoard = true;
	}

	/*@
	 	ensures (\forall Field f; getFields().contains(f);
	 			f.hasRightNeighbor() | f.hasLeftNeighbor() | f.hasOtherNeighbor());
	 	pure
	 */
	/**
	 * Go through the Fields list and assign the neighboring tiles to them.
	 */
	private void linkFields() {
		List<Integer> coord;
		int row, column;
		for (Field f: getFields()) {
			coord = index2Coord(f.getIndex());
			row = coord.get(0);
			column = coord.get(1);
			// has right neighbor if not on the edge
			if (!(column + 1 > row)) {
				f.setRightNeighbor(getField(f.getIndex() + 1));
			}
			// has left neighbor if not on the edge
			if (!(column - 1 < -row)) {
				f.setLeftNeighbor(getField(f.getIndex() - 1));
			}
			// has other/vertical neighbor if not on the edge or if is upsideDown
			if ((row + column) % 2 == 0 && row + 1 < 6) {
				f.setOtherNeighbor(getField(coord2Index(row + 1, column)));
			} else if ((row + column) % 2 == 1) {
				f.setOtherNeighbor(getField(coord2Index(row - 1, column)));
			}
		}
	}

	/*@ 
	 	ensures (0 < index & index < BOARD_SIZE);
	 	pure
 	*/
	/**
	 * Method to check validity of an index.
	 * @param index to be checked number
	 * @return true if index between 0 and 36
	 */
	public boolean isValidIndex(int index) {
		return index >= 0 && index < BOARD_SIZE;
	}
	
	/*@
 	requires isValidIndex(index) & !hasTile(index) & tile != null;
 	pure
	*/
	/**
	 * Checks if the tile can be placed at the given index.
	 * @param index valid index
	 * @param tile valid tile
	 * @return true if tile fits and first tile is not on bonus field
	 * @throws InvalidIndexException if index is not valid
	 */
	public boolean isValidMove(int index, RotatableTile tile) throws InvalidIndexException {
		if (!isValidIndex(index)) {
			throw new InvalidIndexException(index);
		}
		
		boolean validMove = false;
		
		if (isEmptyBoard()) {
			validMove = !getField(index).isBonus();
		} else {
			if (getField(index).isNeighbor() && matchingSides(index, tile) > 0) {
				validMove = true;
			}
		}
		return validMove;
	}
	
	/*@
	 	requires isValidIndex(index) & tile != null;
	 	pure
	 */
	/**
	 * Method for checking the amount of matching sides.
	 * Returning 0 means tile does not fit or is the first turn.
	 * @param index index of field
	 * @param tile tile to be checked for matching sides
	 * @return amount of matching sides
	 */
	public int matchingSides(int index, RotatableTile tile) {
		Field field = getField(index);
		int matchingSides = 0;
		
		if (field.hasLeftNeighbor()) {
			Field left = field.getLeftNeighbor();
			if (left.hasTile()) {
				if (left.getTile().getVariant().getRightSide()
						.isValidAdjacent(tile.getVariant().getLeftSide())) {
					matchingSides++;
				} else {
					// invalid adjacent
					return -1;
				}	
			}
		}
		if (field.hasRightNeighbor()) {
			Field right = field.getRightNeighbor();
			if (right.hasTile()) {
				if (right.getTile().getVariant().getLeftSide()
						.isValidAdjacent(tile.getVariant().getRightSide())) {
					matchingSides++;
				} else {
					// invalid adjacent
					return -1;
				}	
			}
		}
		if (field.hasOtherNeighbor()) {
			Field other = field.getOtherNeighbor();
			if (other.hasTile()) {
				if (other.getTile().getVariant().getOtherSide()
						.isValidAdjacent(tile.getVariant().getOtherSide())) {
					matchingSides++;
				} else {
					// invalid adjacent
					return -1;
				}	
			}
		}
		return matchingSides;
	}
	
	// =========== Calculations ===========

	/**
	 * Method to convert an index representation to corresponding.
	 * coordinate representation of board field in the form of 
	 * (row , column)
	 * @param index valid index to convert to coordinates
	 * @return coord List of integers (in form {[0: row], [1: column]})
	 */
	/*@ pure */ public static List<Integer> index2Coord(int index) {
		List<Integer> result = new ArrayList<>();
		int row = 0;
		int column = 0;

		row = (int) Math.floor((int) (Math.sqrt(index)));
		column = index - (int) Math.pow(row, 2) - row;

		result.add(row);
		result.add(column);
		return result;
	}
	
	/**
	 * Method to convert from coordinate system to index of field
	 * on the board. 
	 * @param row row value
	 * @param column column value
	 * @return calculated index of the field on the board.
	 */
	/*@ pure */ public static int coord2Index(int row, int column) {
		int index = ((int) Math.pow(row, 2)) + row + column;
		return index;
	}
	
	// ============= Getters ==============
	
	/**
	 * Gets the fields.
	 * @return list of fields
	 */
	/*@ pure */ public List<Field> getFields() {
		return fields;
	}
	
	/*@
	 	ensures \result.equals(this);
	 	pure
	 */
	/**
	 * Returns a full copy of the current board.
	 * @return copy of this board
	 */
	public Board copy() {
		Board copy = new Board();
		for (int i = 0; i < BOARD_SIZE; i++) {
			copy.getField(i).putTile(getField(i).getTile());
		}
		return copy;
	}
	
	/*@ 
	 	requires isValidIndex(index);
	 	pure
	 */
	/**
	 * Method that returns the field at an index if it is a 
	 * valid index. 
	 * @param index index of field to be got
	 * @return field field at index
	 */
	public Field getField(int index) {
		return fields.get(index);
	}

	/**
	 * Returns if is empty board.
	 * @return isEmptyBoard
	 */
	/*@ pure */ public boolean isEmptyBoard() {
		return this.emptyBoard;
	}
	
	/*@
	 	ensures (\forall Field field; getFields().contains(field);
	 			field.hasTile()) ==> \result;
	 	pure 
	 */
	/**
	 * Returns if is full board.
	 * @return true if all fields have a tile
	 */
	public boolean isFullBoard() {
		int counter = 0;
		if (!isEmptyBoard()) {
			for (int i = 0; i < BOARD_SIZE; i++) {
				if (getField(i).hasTile()) {
					counter++;
				}
			}
		}
		return counter == BOARD_SIZE;
	}
	
	// ============ Wrappers =============
	
	/**
	 * Wrapper for Field.hasTile() method for easy access.
	 * @param index valid index
	 * @return true if at this index hasTile()
	 */
	/*@ pure */ public boolean hasTile(int index) {
		return getField(index).hasTile();
	}
	
	/**
	 * Wrapper for Field.getTile() method for easy access.
	 * @param index valid index
	 * @return Tile at this field or null
	 */
	/*@ pure */ public RotatableTile getTile(int index) {
		return getField(index).getTile();
	}
	
	/**
	 * Wrapper for Field.setTile(RotatableTile) method for easy access.
	 * @param index valid index
	 * @param tile non-null RotatableTile
	 * @return the updated field
	 */
	public Field setField(int index, RotatableTile tile) {
		getField(index).putTile(tile);
		return getField(index);
	}

	/**
	 * Sets emptyBoard to false.
	 */
	public void unEmptyBoard() {
		this.emptyBoard = false;
	}
	
}
