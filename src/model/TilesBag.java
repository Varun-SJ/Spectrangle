package model;

import java.util.ArrayList;
import java.util.Random;

/**
 * TilesBag class for keeping track of the tiles that are not yet on the board or in a 
 * players hand.
 * @author Corjan van den Brink
 * @author Varun Sudhakar
 * @version 2019.01.26
 */
public class TilesBag {

	private ArrayList<RotatableTile> tiles;
	private Random rand;

	/**
	 * Creates a bag and fills it with the Spectrangle tiles.
	 */
	public TilesBag() {
		tiles = new ArrayList<>();
		rand = new Random();
		fillStartingBag();
	}

	/**
	 * Adds a tile to the bag.
	 * @param tile to be added
	 */
	public void addTile(RotatableTile tile) {
		tiles.add(tile);
	}

	/**
	 * Gets bag size or remaining tiles amount.
	 * @return amount of remaining tiles
	 */
	public int getBagSize() {
		return tiles.size();
	}
	
	/**
	 * Gets if empty bag.
	 * @return true if no tiles in bag
	 */
	public boolean isEmpty() {
		return tiles.isEmpty();
	}
	
	/**
	 * Removes a random tile from the bag and returns it.
	 * @return A random tile that was removed from the bag.
	 */
	public RotatableTile takeRandomTile() {
		return tiles.remove(rand.nextInt(getBagSize()));

	}

	/**
	 * Populates the bag initially with all valid tiles.
	 */
	public void fillStartingBag() {

		int points;
		// All sides have different colors

		/*
		 * 1 point tiles.
		 * Joker: WWW
		 * GRP tile 
		 * BYG tile 
		 * RYB tile
		 */

		points = 1;

		addTile(new RotatableTile(Color.W, Color.W, Color.W, points)); // Joker Tile
		addTile(new RotatableTile(Color.G, Color.R, Color.P, points));
		addTile(new RotatableTile(Color.B, Color.Y, Color.G, points));
		addTile(new RotatableTile(Color.R, Color.Y, Color.B, points));

		/*
		 * 2 point tiles. 
		 * BRP 
		 * YPR 
		 * YPG
		 */

		points = 2;

		addTile(new RotatableTile(Color.B, Color.R, Color.P, points));
		addTile(new RotatableTile(Color.Y, Color.P, Color.R, points));
		addTile(new RotatableTile(Color.Y, Color.P, Color.G, points));

		/*
		 * 3 point tiles. 
		 * YBP 
		 * RGY 
		 * BGP 
		 * GRB
		 */

		points = 3;

		addTile(new RotatableTile(Color.Y, Color.B, Color.P, points));
		addTile(new RotatableTile(Color.R, Color.G, Color.Y, points));
		addTile(new RotatableTile(Color.B, Color.G, Color.P, points));
		addTile(new RotatableTile(Color.G, Color.R, Color.B, points));

		// Two sides of the tile have same color

		/*
		 * 4 point tiles. 
		 * RRB
		 * RRG 
		 * BBG 
		 * BBY 
		 * GGY 
		 * GGP 
		 * YYR 
		 * YYP 
		 * PPR 
		 * PPB
		 */

		points = 4;

		addTile(new RotatableTile(Color.R, Color.R, Color.B, points));
		addTile(new RotatableTile(Color.R, Color.R, Color.G, points));
		addTile(new RotatableTile(Color.B, Color.B, Color.G, points));
		addTile(new RotatableTile(Color.B, Color.B, Color.Y, points));
		addTile(new RotatableTile(Color.G, Color.G, Color.Y, points));
		addTile(new RotatableTile(Color.G, Color.G, Color.P, points));
		addTile(new RotatableTile(Color.Y, Color.Y, Color.R, points));
		addTile(new RotatableTile(Color.Y, Color.Y, Color.P, points));
		addTile(new RotatableTile(Color.P, Color.P, Color.R, points));
		addTile(new RotatableTile(Color.P, Color.P, Color.B, points));

		/*
		 * 5 point tiles. 
		 * RRY 
		 * RRP 
		 * BBR 
		 * BBP 
		 * GGR 
		 * GGB 
		 * YYG 
		 * YYB 
		 * PPY 
		 * PPG
		 */

		points = 5;

		addTile(new RotatableTile(Color.R, Color.R, Color.Y, points));
		addTile(new RotatableTile(Color.R, Color.R, Color.P, points));
		addTile(new RotatableTile(Color.B, Color.B, Color.R, points));
		addTile(new RotatableTile(Color.B, Color.B, Color.P, points));
		addTile(new RotatableTile(Color.G, Color.G, Color.R, points));
		addTile(new RotatableTile(Color.G, Color.G, Color.B, points));
		addTile(new RotatableTile(Color.Y, Color.Y, Color.B, points));
		addTile(new RotatableTile(Color.Y, Color.Y, Color.G, points));
		addTile(new RotatableTile(Color.P, Color.P, Color.Y, points));
		addTile(new RotatableTile(Color.P, Color.P, Color.G, points));

		// Three sides have the same color

		/*
		 * 6 point tiles. 
		 * PPP 
		 * YYY 
		 * BBB 
		 * GGG 
		 * RRR
		 */

		points = 6;

		addTile(new RotatableTile(Color.P, Color.P, Color.P, points));
		addTile(new RotatableTile(Color.Y, Color.Y, Color.Y, points));
		addTile(new RotatableTile(Color.B, Color.B, Color.B, points));
		addTile(new RotatableTile(Color.G, Color.G, Color.G, points));
		addTile(new RotatableTile(Color.R, Color.R, Color.R, points));

	}
}
