package nl.tudelft.jpacman;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import nl.tudelft.jpacman.board.Direction;
import nl.tudelft.jpacman.game.Game;
import nl.tudelft.jpacman.level.Player;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;


@SuppressWarnings("magicnumber")
public class Part4Test {
	
	private Launcher launcher;
	

	/**
	 * Launch the user interface.
	 */
	@Before
	public void setUpPacman() {
		launcher = new Launcher();
		launcher.launch();
	}
	
	/**
	 * Quit the user interface when we're done.
	 */
	@After
	public void tearDown() {
		launcher.dispose();
	}

    /**
     * Launch the game, and imitate what would happen in a typical game.
     * The test is only a smoke test, and not a focused small test.
     * Therefore it is OK that the method is a bit too long.
     * 
     * @throws InterruptedException Since we're sleeping in this test.
     */
     
     //NOTE: game.move(player, Direction.direction)
     //NOTE: move(game, Direction.direction, number of steps)
    @SuppressWarnings({"methodlength", "PMD.JUnitTestContainsTooManyAsserts"})
    @Test
    public void smokeTest() throws InterruptedException {
        Game game = launcher.getGame();        
        Player player = game.getPlayers().get(0);
 
        // start cleanly.
        assertFalse(game.isInProgress());
        game.start();
        assertTrue(game.isInProgress());
        assertEquals(0, player.getScore());
	
	
	//Try to freeze the game(stopping all NPCs at this point, mark should remain unchanged)
	game.stopNPCsGame();
	assertEquals(0,player.getScore());
	assertTrue(player.isAlive());
        assertTrue(game.isInProgress());
	
	//Now the NPCs have been frozen 
	
	//Frozen,Alive
        //game.move should affect and should  get 10  points
        game.move(player, Direction.EAST);
        assertEquals(10, player.getScore());
	assertTrue(game.isInProgress());
	
        //Frozed,Alive
        //Case A: Under freezing, try moving to get all the scores in a certain path before encountering the ghost
	//Sub-step of A: try to move as north as we can 
        move(game, Direction.NORTH,4);
        assertEquals(30, player.getScore());
	
	//Frozen,Alive
	//Sub-step of A continues: try to move to east by 3 steps
	move(game, Direction.EAST,3);
	assertEquals(60,player.getScore());
	
	//Frozen,Alive
	//Sub-Step of A continues: try to move to north to hit the end
	//But there are no points to be gained along this subpath
	move(game,Direction.NORTH,15);
	assertEquals(60,player.getScore());
	assertTrue(player.isAlive());
	
	//Frozen,Dead
	//move a left turn to encountered the ghost
	move(game,Direction.WEST,15);
	assertEquals(60,player.getScore());
	assertFalse(player.isAlive()); 	                


	 
	//Frozen,Dead
	//Now the player has encountered the ghost, further movement should not results in 
	//changing the scores(plus,there should not be movements allowed)
	move(game,Direction.EAST,3);
	assertEquals(60,player.getScore());
	
	//Frozen,Dead
	//Try to encounter the yellow dots go get scores(which is not allowed)
	move(game,Direction.NORTH,5);
	assertEquals(60,player.getScore());
	
	//Frozen, Dead
	move(game,Direction.WEST,6);
	assertEquals(60,player.getScore());
	assertFalse(player.isAlive()); 
	
	//Unfrozen, Dead,should not change scores while pressed the unfreeze button..
	game.startNPCsGame();
	assertEquals(60,player.getScore());
	assertFalse(player.isAlive());		 			
	
	
	
	//Try to move while all the NPCs are unfrozed and compare the score
	//To folloing case must cover the possibilies that hypothesistically, the pacman will encounter
	//at least one yellow dot, despite of his initial position, given the fact that
	//the yellow dots are sufficient to be tested.	
	move(game,Direction.NORTH,10);
	move(game,Direction.EAST,10);
	move(game,Direction.SOUTH,10);
	move(game,Direction.WEST,10);
	move(game,Direction.NORTH,10);
	move(game,Direction.EAST,10);
	move(game,Direction.SOUTH,10);
	move(game,Direction.WEST,10);
	move(game,Direction.NORTH,10);
	move(game,Direction.EAST,10);
	move(game,Direction.SOUTH,10);
	move(game,Direction.WEST,10);
	move(game,Direction.NORTH,10);
	move(game,Direction.EAST,10);
	move(game,Direction.SOUTH,10);
	move(game,Direction.WEST,10);
	assertFalse(player.isAlive());
	assertEquals(60,player.getScore());
	
	//stop('pause') the game  
        game.stop();
        assertFalse(game.isInProgress());
     }

    /**
     * Make number of moves in given direction.
     *
     * @param game The game we're playing
     * @param dir The direction to be taken
     * @param numSteps The number of steps to take
     */
    public static void move(Game game, Direction dir, int numSteps) {
        Player player = game.getPlayers().get(0);
        for (int i = 0; i < numSteps; i++) {
            game.move(player, dir);
        }
    }
}

