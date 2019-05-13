package controller;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Scanner;

import model.*;

/**
 * Human player controller for the game, mostly validating input from the console
 * and parsing this to a move that is readable by the game.
 * @author Corjan van den Brink
 * @author Arne de Roode
 * @version 2019.01.30
 */
public class HumanPlayer extends Player {

	private static String usageInstructions = "Now determine your move... "
			+ "Provide your move in either of the three following formats: \n" +
            "   place <tile> <index> <orientation>   (index can have value between 0-35, "
            	+ "orientation can have value R/L/O) \n" +
            "   discard <tile> \n" +
                "pass";
	
	public HumanPlayer(String name) {
		super(name);
	}

	/**
	 * Method for providing the current status, suggesting a move using a computer strategy
	 * and validating the created move by the player. 
	 * @param board the game board
	 * @return valid move created by the user
	 */
	@Override
	public Move determineMove(Board board) {
        // your tiles
        System.out.println("Your tiles: ");
        String tileString = "";
        String tiles = "Your tiles: ";
        for (RotatableTile tile : getTiles()) {
            tileString = tileString.concat(tile.getTileString());
            tile.flip();
            tileString = tileString.concat(tile.getTileString());
            tiles = tiles.concat(tile.toString()) + " ";
        }
        System.out.println(tileString);
        System.out.println(tiles);

	    // suggest move
        System.out.println("You could do the following move: (type \"hint\" to use this move) ");
        Strategy strategy = new NaiveStrategy();
        Move suggestMove = strategy.determineMove(this.getTiles(), board);
        suggestMove.getTile().applyVariant(suggestMove.getVariant());

        switch (suggestMove.getType()) {
            case PLACE: {
                System.out.println("   Type: " + suggestMove.getType().toString().toLowerCase() +
                		"\n" + "   Tile: " + suggestMove.getTile().toString() + "\n" +
                        "   Index: " + suggestMove.getIndex() + "\n" +
                        "   Rotation: " + suggestMove.getTile().getRotation().toString());
                break;
            }
            case DISCARD: {
                System.out.println(suggestMove.getType().toString().toLowerCase() + " " + 
                		suggestMove.getTile().toString());
                break;
            }
            case PASS: {
                System.out.println(suggestMove.getType().toString().toLowerCase());
            }
        }

        // ask for move
        Move move = createMove(usageInstructions);
        if (move == null) {
        	return suggestMove;
        } else {
	        try {
	        	MoveType type = move.getType();
	        	switch (type) {
	        		case PLACE:
	        			RotatableTile tile = move.getTile();
	                	tile.applyVariant(move.getVariant());
	        			while (!board.isValidMove(move.getIndex(), tile)) {
	        				createMove("Wrong move: This tile with this rotation cannot be "
	        						+ "placed here.");
	        			}
	        			break;
	        		case DISCARD:
	        			if (!getTiles().contains(move.getTile())) {
	        				createMove("Wrong move: You do not own this tile.");
	        			}
	        			if (suggestMove.getType() == MoveType.PLACE) {
	        				createMove("Wrong move: You cannot discard when a valid move "
	        						+ "can be placed.");
	        			}
	        			break;
	        		case PASS:
	        			if (suggestMove != null) {
	        				createMove("Wrong move: You cannot pass while there are valid moves.");
	        			}
	        	}
			} catch (InvalidIndexException e) {
				//should not occur as is checked in createMove()
			}
        }
	    return move;
	}

	/**
	 * Method for parsing the input from the user into a move.
	 * @param instructions question or instruction to the user
	 * @return Move containing the information the user has provided
	 */
	private Move createMove(String instructions) {
        System.out.println(instructions);

        try (Scanner scanner = new Scanner(readString("> "))) {
        	if (scanner.hasNext()) {
    	        String moveType = scanner.next();
    	        switch (moveType) {
                    case "place": {
                        if (scanner.hasNext()) {
                            String tileString = scanner.next();
                            RotatableTile tile = findTileByString(tileString);

                            if (tile == null) {
                                return createMove("Error: You do not own this tile");
                            } else {
                                if (scanner.hasNext()) {
                                    int index;
                                    int row = 0;
                                    int column = 0;
                                    try {
                                        index = Integer.parseInt(scanner.next());
                                        List<Integer> coords = Board.index2Coord(index);
                                        row = coords.get(0);
                                        column = coords.get(1);

                                    } catch (NumberFormatException e) {
                                        index = -1;
                                    }
                                    if (index < 0 || index > 35) {
                                        return createMove("Error: Invalid index provided");
                                    } else {
                                        if (scanner.hasNext()) {
                                            String rotation = scanner.next();

                                            if (rotation.equals("R") || rotation.equals("O") || 
                                            		rotation.equals("L")) {

                                                boolean isUpsideDown = ((row + column) % 2) == 1;

                                                String key = "";
                                                if (isUpsideDown) {
                                                    key = key.concat("U");
                                                }
                                                key = key.concat(rotation);

                                                return new Move(MoveType.PLACE, index, tile, 
                                                		tile.getVariant(key));
                                               
                                            } else {
                                                return createMove("Error: "
                                                		+ "Invalid rotation provided");
                                            }

                                        } else {
                                            return createMove("Error: Invalid input");
                                        }
                                    }
                                } else {
                                    return createMove("Error: Invalid input");
                                }
                            }

                        } else {
                            return createMove("Error: Invalid input");
                        }
                    }
                    case "discard": {
                        if (scanner.hasNext()) {
                            String tileString = scanner.next();
                            RotatableTile tile = findTileByString(tileString);

                            if (tile == null) {
                                return createMove("Error: You do not own this tile");
                            } else {
                                try {
                                    return new Move(MoveType.DISCARD, tile);
                                } catch (InvalidMoveException e) {
                                    //should not occur
                                    return null;
                                }
                            }

                        } else {
                            return createMove("Error: Invalid input");
                        }

                    }
                    case "pass": {
                        try {
                            return new Move(MoveType.PASS);
                        } catch (InvalidMoveException e) {
                            // should not occur
                            return null;
                        }

                    }
                    case "hint":
                    	return null;
                    default: {
                        System.out.println("Invalid input");
                        return createMove(instructions);
                    }
                }
            } else {
                System.out.println("Invalid input");
                return createMove(instructions);
            }
        } catch (NoSuchElementException e) {
        	// never accessed
        	return createMove(usageInstructions);
        }
       
    }

    /**
     * read a line from the default input.
     * @param text prompt for this user input
     * @return response of the user
     */
    static public String readString(String text) {
        System.out.print(text);
        String resp = null;
        try {
            BufferedReader in = new BufferedReader(new InputStreamReader(
                    System.in));
            resp = in.readLine();
        } catch (IOException e) {
        }

        return (resp == null) ? "" : resp;
    }

}
