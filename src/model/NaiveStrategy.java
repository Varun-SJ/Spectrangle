package model;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Random;

import controller.InvalidIndexException;
import controller.InvalidMoveException;

/**
 * Naive strategy for computer player, makes a random valid move.
 * @author Corjan van den Brink
 * @version 2019.01.28
 */
public class NaiveStrategy implements Strategy {

	private final static String NAME = "Naive";
	private Random rand = new Random();
	
	@Override
	/*@ pure */ public String getName() {
		return NaiveStrategy.NAME;                            
	}

	/**
	 * Finds a random valid move for the player. If no place moves are found, discards and 
	 * pass are added.
	 */
	@Override
	public Move determineMove(List<RotatableTile> tiles, Board board) {
		// find all place moves
		List<Move> validMoves = findPlaceMoves(tiles, board);

		// add pass and discards if necessary		
		if (validMoves.size() == 0) {
			try {
				validMoves.add(new Move(MoveType.PASS));
			} catch (InvalidMoveException e) {
				// should not occur
			}
			int i = 0;
			for (RotatableTile tile: tiles) {
				try {
					validMoves.add(i++, new Move(MoveType.DISCARD, tile));
				} catch (InvalidMoveException e) {
					// should not occur
				}
			}
		}

		// Pick a random valid move and return this one
		Move move = validMoves.get(rand.nextInt(validMoves.size()));
		
		return move;		
	}

	public List<Move> findPlaceMoves(List<RotatableTile> tiles, Board board) {

		List<Field> fields = board.getFields();
		List<Move> validMoves = new ArrayList<>();

		/*
		 * For all tiles from the player, check all variants to the fields. If a valid
		 * move is found, save it.
		 */

		for (RotatableTile tile: tiles) {
			Map<String, SimpleTile> variants = tile.getVariants();
			Iterator<String> it = variants.keySet().iterator();
			while (it.hasNext()) {
				String key = it.next();
				SimpleTile variant = variants.get(key);
				tile.applyVariant(variant);
				for (int i = 0; i < fields.size(); i++) {
					try {
						if (board.getField(i).isUpsideDown() == tile.isUpsideDown() &&
								board.isValidMove(i, tile)) {
							validMoves.add(new Move(MoveType.PLACE, i, tile, variant));
						}
					} catch (InvalidIndexException e) {
						// Disregard as fields.size() == 36
					}
				}
			}
		}

		return validMoves;
	}

}
