package model;

import controller.InvalidMoveException;

/**
 * Move class is used to store all relevant information for a move, such that it can be
 * validated and placed afterwards.
 * @author Corjan van den Brink
 * @version 2019.01.30
 */
public class Move {
	
	private MoveType type;
	private int index;
	private RotatableTile tile;
	private SimpleTile variant;
	
	/*
	 * Move constructors for the 3 types of moves, throw InvalidMoveExceptions when 
	 * the wrong constructor is called.
	 */
	
	public Move(MoveType type, int index, RotatableTile tile, SimpleTile variant) {
		this.type = type;
		this.index = index;
		this.tile = tile;
		this.variant = variant;
	}
	
	public Move(MoveType type, RotatableTile tile) throws InvalidMoveException {
		if (type != MoveType.DISCARD) {
			throw new InvalidMoveException(type);
		}
		this.type = type;
		this.tile = tile;
	}
	
	public Move(MoveType type) throws InvalidMoveException {
		if (type != MoveType.PASS) {
			throw new InvalidMoveException(type);
		}
		this.type = type;
	}

	/**
	 * Getter for MoveType.
	 * @return MoveType.PLACE, DISCARD or PASS
	 */
	public MoveType getType() {
		return type;
	}

	/**
	 * Getter for index.
	 * @return index
	 */
	public int getIndex() {
		return index;
	}

	/**
	 * Getter for Rotatable tile.
	 * @return tile
	 */
	public RotatableTile getTile() {
		return tile;
	}
	
	/**
	 * Getter for ST variant.
	 * @return variant
	 */
	public SimpleTile getVariant() {
		return variant;
	}
	
}
