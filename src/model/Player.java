package model;

import java.util.ArrayList;
import java.util.List;

/**
 * Abstract player class for building players with.
 * @author Varun Sudhakar
 * @author Corjan van den Brink
 * @author Arne de Roode
 * @version 2019.01.30
 */
public abstract class Player {
	
	private String name;
	private int points;
	protected List<RotatableTile> tiles;
	
	public Player(String name) {
		this.name = name;
		this.points = 0;
		tiles = new ArrayList<>();
	}
	
	/**
	 * Should find a valid move to play on the board.
	 * @param board board status for determining moves
	 * @return a move (index, tile variant)
	 */
	public abstract Move determineMove(Board board);

	/*@
	 	ensures getPoints() == \old(getPoints() + amount);
	 */
	/**
	 * Adds amount of points to this player.
	 * @param amount to be added points
	 */
	public void addPoints(int amount) {
		points = getPoints() + amount;
	}

	/*@
	 	ensures getTiles().contains(tile);
	 */
	/**
	 * Adds tile to the player's tiles.
	 * @param tile tile to add
	 */
	public void addTile(RotatableTile tile) {
		tiles.add(tile);	
	}

	/*@
		ensures !getTiles().contains(tile);
	 */
	/**
	 * Removes tile from the player's tiles.
	 * @param tile tile to remove
	 */
	public void removeTile(RotatableTile tile) {
		tiles.remove(tile);	
	}

	/**
	 * Removes all tile from the player's tiles.
	 */
	public void removeTiles() {
		tiles.clear();
	}

	/**
	 * Getter for name.
	 * @return name
	 */
	/*@ pure */ public String getName() {
		return this.name;
	}

	/**
	 * Getter for points.
	 * @return points
	 */
	/*@ pure */ public int getPoints() {
		return this.points;
	}

	/**
	 * Getter for tiles.
	 * @return List of tiles
	 */
	/*@ pure */ public List<RotatableTile> getTiles() {
		return tiles;
	}
	
	/**
	 * Finds a tile by its string representation.
	 * @param strRep string representation for tile
	 * @return the tile represented by this string
	 */
	public RotatableTile findTileByString(String strRep) {
		for (RotatableTile tile : tiles) {
			if (tile.toString().equals(strRep)) {
				return tile;
			}
		}

		return null;
	}
}
