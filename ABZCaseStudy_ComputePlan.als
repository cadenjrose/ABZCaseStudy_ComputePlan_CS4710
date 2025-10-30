module ABZCaseStudy_ComputePlan

/* 
File-------------------+ ABZCaseStudy_ComputePlan_CS4710.als
Course--------------+ Model Driven Software Development (Michigan Tech CS4710)
Author(s)-----------+ Seamus Barry, John Bowie, Conner Born, Caden Rose
Semester-----------+ Fall 2025
Date Created------+ 10/29/2025
Description---------+This Alloy module aims to model the ComputePlan modules of the ABZ 2026 Case Study: "A Planetary Rover".
-------------------------The Rover's mission is to visit each of the 'Goal's without running into an obsticle or running out of charge. A path of
-------------------------x,y coordinates is the output of the path calculation. If the Rover calculates paths with the same cost, the path that 
-------------------------leaves the Rover with the most amount of charge will be selected.
-------------------------see https://github.com/trarse-nii/ABZ2026-case-study/blob/main/doc/document_v1.pdf for more information
*/

open util/ordering[XCoord] // orders the x-coordinates
open util/ordering[YCoord] // orders the y-coordinates
open util/ordering[ChargeLevel] // orders the charge levels

// pseudo integers
enum XCoord {x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10} // can expand later
enum YCoord {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10} // can expand later 
enum ChargeLevel {c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10} // can expand later


// -------------- Signatures  -------------- //


// 2D position
sig Position {
	x: one XCoord,	// The x-coordinate
	y: one YCoord		// The y-coordinate
}

// Objects on the Map that have a position
sig MapObject {
	location: one Position	// The objects location
}

sig Goal extends MapObject {}		// The Goal Objects
sig Charger extends MapObject {}	// The Charger Objects
sig Obstacle extends MapObject {}       // The Obstacle Objects

// The calculated Path to reach all Goals without running out of Charge
sig Path {
	positions: set Position,				// The set of positions in the path
	start: one Position,					// The initial position
	end: one Position,					// The terminal position
	nextPos: positions -> lone positions	// The order of positions
}

// The current state of the Rover
sig Rover {
	var currentPos: one Position,		// The current x,y position
	var charge: one ChargeLevel,	// The current charge
	var currentPath: one Path		// The current path
}

// A map object the rover can traverse
sig Map {
	obstacles: set Obstacle,	// The set of obstacles
	chargers: set Charger,	// The set of chargers
	goals: set Goal		// The set of goals
}
one sig ActiveMap extends Map {} // The Map the Rover is activly traversing


// ----------------- Facts  ------------------//


fact {
	// Initialize the rover
	InitRover 

	// Select the Map
	SelectMapOne

	// Initialze the currentPath to only be the starting position
	Rover.currentPath.positions = Path.start

	 // Every path has a valid structure
	always ValidPathStructure

	// There are never any extra map objects other than the ones defined by each map
	always no m: MapObject | m not in ActiveMap.(obstacles + goals + chargers)

	// The map never dynamically changes
	always StaticMap 

	// The active map is the only map
	always Map = ActiveMap

	// One step is always taken
	always oneStep

	always #Rover = 1
}


// -------------- Predacates --------------//

/* Initializes the Rover */
pred InitRover {
	// Rover starts at position (x0, y0) with charge c10
	some r: Rover, pos: Position | {
		pos.x = x0
		pos.y = y0
		r.currentPos = pos
		r.charge = c10
	}
}

/* Is the path structure valid? */
pred ValidPathStructure {all p: Path | ValidPathStructure[p]}
pred ValidPathStructure[p: Path] {
	// The start point has no previous positon
	no p.start.~(p.nextPos)

	// The end point has no next position
	no p.end.(p.nextPos)

	// All positions that are not the end position have one next position
	all pos: (p.positions - p.end) | one pos.(p.nextPos)

	// All positions are reachable from the starting position
	p.positions = p.start.*(p.nextPos)

	// There are never any obstacles inside of a Rover's current path
	no (ActiveMap.obstacles.location & Rover.currentPath.positions)
}

/* Does an operation get taken? */
pred oneStep {
	lowerCharge or
	always doNothing
}

/* Do we do nothing? */
pred doNothing {
	currentPos' = currentPos
	charge' = charge
	currentPath' = currentPath
}

/* Does the Map stay dynamically unchanged? */
pred StaticMap {
	Obstacle' = Obstacle
	obstacles' = obstacles
	Charger' = Charger
	chargers' = chargers
	Goal' = Goal
	goals' = goals
	location' = location
	Position' = Position
	Map' = Map
}

/* Does Rover r lower its charge at this time? */
pred lowerCharge {some r: Rover | lowerCharge[r]}
pred lowerCharge[r: Rover] {
	// Pre-conditions
	r.charge != c0 // r must have some charge

	// Post-conditions
	r.charge' = prev[r.charge]
}


// ------------------ Maps -----------------//


/* 
	Expected Path: (x0, y0), (x0, y1), (x0, y2), (y2, x1), (x2, y2)
	Note* map only looks visually appealing in the Alloy text editor

	y2     + - - - - - - - - - - - ->Goal
		 |
		 |
	y1	 |	   Obstacle
		 |
		 |
	y0  Start	   Obstacle
		x0		x1		x2
 */
pred SelectMapOne {some o1: Obstacle, o2: Obstacle - o1,  g: Goal, c: Charger | SelectMapOne[o1, o2, g, c]}
pred SelectMapOne[o1: Obstacle, o2: Obstacle, g: Goal, c: Charger] {
	// Obstacles
	o1.x = x1 and o1.y = y1
	o2.x = x1 and o2.y = y0
	ActiveMap.obstacles = o1 + o2

	// Goals
	g.x = x2 and g.y = y2
	ActiveMap.goals = g

	// Chargers
	c.x = x0 and c.y = y2
	ActiveMap.chargers = c
}

/* 
	Expected Path: (x0, y0), (x0, y1), (x0, y2), (x0, y3), (x0, y4), (x1, y4), (x2, y4), (x2, y3), (x2, y2), (x3, y2), (x4, y2), (x4, y3), (x4, y4)
	Note* map only looks visually appealing in the Alloy text editor

	y4  Goal - - - - - - - - - - - - +			     Goal
		 |				  |				 ^
		 |				  |				 |
	y3	 |          Obstacle        |        Obstacle        |
		 |				  |				 |
		 |				  |				 |
	y2     |			     Charge - - - - - - - - - - +
		 |
		 |
	y1	 |
		 |
		 |
	y0  Start	   
		x0		x1		x2		x3		x4
 */
pred SelectMapTwo {some o1: Obstacle, o2: Obstacle - o1, o3: Obstacle - (o1+o2), g1: Goal, g2: Goal - g1, c: Charger | SelectMapTwo[o1, o2, o3, g1, g2, c]}
pred SelectMapTwo [o1: Obstacle, o2: Obstacle, o3: Obstacle, g1: Goal, g2: Goal, c: Charger] {
	// Obstacles
	o1.x = x3 and o1.y = y3
	o2.x = x3 and o2.y = y4
	o3.x = x1 and o3.y = y3
	ActiveMap.obstacles = o1 + o2 + o3
	
	// Goals
	g1.x = x0 and g1.y = y4
	g2.x = x4 and g2.y = y4
	ActiveMap.goals = g1 + g2

	// Chargers
	c.x = x2 and c.y = y2
	ActiveMap.chargers = c
}


pred ComputePlan [r: Rover] {
	// Compute the path
}

// -------------- Functions --------------//


// Returns the x coordinate of the map object
fun x[m: MapObject]: one XCoord {
	m.location.x
}


// Returns the y coordinate of the map object
fun y[m: MapObject]: one YCoord {
	m.location.y
}

pred show {}
run show for 8


