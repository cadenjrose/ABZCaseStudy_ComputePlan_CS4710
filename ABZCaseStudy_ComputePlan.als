module ABZCaseStudy_ComputePlan

/* 
File-------------------+ ABZCaseStudy_ComputePlan_CS4710.als
Course--------------+ Model Driven Software Development (Michigan Tech CS4710)
Author(s)-----------+ Seamus Barry, John Bowie, Conner Born, Caden Rose (Team Junior Mints)
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
enum YCoord {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10}  // can expand later
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
var sig visited in Goal {}
sig Charger extends MapObject {}  	// The Charger Objects
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
	obstacles: set Obstacle,	// The set of obstacles (switch to var when doing dynamic map)
	chargers: set Charger,	// The set of chargers
	goals: set Goal,		// The set of goals
	topEdge: one YCoord,   // The maximum traversable y value
	rightEdge: one XCoord   // The maximum traversable x value
}
one sig ActiveMap extends Map {} // The Map the Rover is activly traversing


// ----------------- Facts  ------------------//


fact {
	 // Every path has a valid structure
	ValidPathStructure

	// No positions have the same x and y values
	all disj p1, p2: Position | p1.x != p2.x or p1.y != p2.y

	// There are no extra map objects other than the ones defined by each map
	no m: MapObject | m not in ActiveMap.(obstacles + goals + chargers)

	// The rovers charge is greater than c0
	always gt[Rover.charge, c0]

	// The active map is the only map
	always Map = ActiveMap
}


// -------------- Predacates --------------//

/* Initializes the Rover */
pred InitRover {
	// Rover starts at position (x0, y0) with charge c10
	some r: Rover | {
		r.currentPos.x = x0
		r.currentPos.y = y0
		r.charge = c10
		r.currentPath.start = r.currentPos // current path starts at x0, y0
	}

	// There is only ever 1 rover
	always #Rover = 1

	

	// The rover never runs out of battery (maybe it can)
	--always gt[Rover.charge, c0]
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

	// All positions that are not the start position have a prev position
	all pos: (p.positions - p.start) | one pos.~(p.nextPos)

	// All positions are reachable from the starting position
	p.positions = p.start.*(p.nextPos)

	// All next positions must be adjacent
	adj[p.nextPos]

	// The path never goes out of bounds
	all pos: p.positions | lte[pos.x, ActiveMap.rightEdge] and lte[pos.y, ActiveMap.topEdge]

	// There are no obstacles inside of a Rover's current path
	no (ActiveMap.obstacles.location & Rover.currentPath.positions)

	// There is only ever one path, the current path
	#Path = 1
	
	// There are no visited goals at the start
	no visited

	// Every goal must be in the path
	ActiveMap.goals.location in p.positions
}


// -------- Temporal Predicates-------//

-- Tried this but couldn't get to work
/*
pred RandomObstacleAppears{some o: Obstacle | RandomObstacleAppears[o]}
pred RandomObstacleAppears[o: Obstacle] {
	-- Pre-conditions
		// The obstacle does not already exist
		o not in ActiveMap.obstacles
	
		// The obstacle does not share a location to any map object or the rover
		no o.location & (ActiveMap.(goals+chargers+obstacles).location + Rover.currentPos)
	
		// The obstacle is in-bounds
		lte[o.location.x, ActiveMap.rightEdge]
		lte[o.location.y, ActiveMap.topEdge]

	-- Post-conditions (changed)
		ActiveMap.obstacles' = ActiveMap.obstacles + o

	-- Post-conditions (unchanged)
		visited' = visited
		currentPos' = currentPos
		charge' = charge
		currentPath' = currentPath
}
*/



pred TakeStep {some r: Rover | TakeStep[r]}
pred TakeStep[r: Rover] {
	-- There is no obstacle in the next position
	no r.nextStep & ActiveMap.obstacles.location
	-- The rover must have at least 1 charge to take a step
	gt[r.charge, c0]

	-- A charger in the next step means that charge is reset in the next step
	(one c: ActiveMap.chargers | c.location = r.nextStep) implies (r.charge' = c10)
	-- Otherwise, the charge is decremented
	(no c: ActiveMap.chargers | c.location = r.nextStep) implies (r.charge' = prev[r.charge])	

	(one g: ActiveMap.goals | g.location = r.nextStep) implies (one g: ActiveMap.goals | visited' = visited + g)
	(no g: ActiveMap.goals | g.location = r.nextStep) implies (visited' = visited)

	-- CurrentPos is the next step location
	r.currentPos' = r.nextStep

	-- Unchanged
	r.currentPath' = r.currentPath
	--ActiveMap.obstacles' = ActiveMap.obstacles
}

// ------------------ Maps -----------------//


/* 
	Expected Path: (x0, y0), (x0, y1), (x0, y2), (x1, y2), (x2, y2)
	Note* map only looks visually appealing in the Alloy text editor

	y2 Charger - - - - - - - - - ->Goal
		 |
		 |
	y1	 |	   Obstacle
		 |
		 |
	y0  Start	   Obstacle
		x0		x1		x2
 */
pred SelectMapOne {some o1: Obstacle, o2: Obstacle - o1, g: Goal, c: Charger | SelectMapOne[o1, o2, g, c]}
pred SelectMapOne[o1: Obstacle, o2: Obstacle, g: Goal, c: Charger] {
	// Set Map Boundary
	ActiveMap.rightEdge = x2
	ActiveMap.topEdge = y2

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

	y4  Goal - - - - - - - - - - - - +	   Obstacle     Goal
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
	// Set Map Boundary
	ActiveMap.rightEdge = x4
	ActiveMap.topEdge = y4

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

/* Does nothing happen? */
pred DoNothing {
	visited' = visited
	currentPos' = currentPos
	currentPath' = currentPath
	--obstacles' = obstacles
	charge' = charge
}

/* Does the rover launch? */
pred LaunchRover {
	InitRover -- Initialize Rover
	always (visited != ActiveMap.goals implies TakeStep) -- Take steps until all goals have been reached
	eventually always DoNothing -- Eventually do nothing forever
}


/* Are two positions adjacent to each other? */
pred adj[p: Position -> Position] {
	all a, b: Position | a->b in p implies (
		((a.x = next[b.x] or a.x = prev[b.x]) and (a.y = b.y)) or
    		((a.y = next[b.y] or a.y = prev[b.y]) and (a.x = b.x))
  	)
}

/* Is a Plan/Scenario Chosen? */
pred ChooseScenario {
	ComputePlan_MapOne or
	ComputePlan_MapTwo
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

// Returns the position the rover will traverse to next
fun nextStep[r: Rover]: Position {
	 r.currentPos.(r.currentPath.nextPos)
}

// --------------- Assertions -------------//

// There are no cycles in the path other than the end position
assert NoPathCycles {
	all p: Path |
		all pos: p.positions - p.end |
			always one pos.(p.nextPos)
}
--check NoPathCycles for 12 but 1 Path, 1 Rover, 1 Map

// The beginning and ending positions are unique and correct
assert ValidStartEndPoints {
	all p: Path | (
		always (
			one p.start and one p.end and
			no p.start.~(p.nextPos) and
			no p.end.(p.nextPos)
		)
	)
}
--check ValidStartEndPoints for 12 but 1 Path

// Rover can only move if it has charge
assert NoMoveOnZeroCharge {
	all r: Rover |
		always (lte[r.charge, c0] implies r.currentPos' = r.currentPos)
}
--check NoMoveOnZeroCharge for 10 steps

// Rover always stays in bounds
assert RoverStaysInBounds {
	ChooseScenario implies (
		always (
			lte[Rover.currentPos.x, ActiveMap.rightEdge] and
			lte[Rover.currentPos.y, ActiveMap.topEdge]
		)   
	)
}
--check RoverStaysInBounds for 10 steps

// --------- Run-able Scenarios  -------//

/* Launch Rover in MapOne */
pred ComputePlan_MapOne {
	 -- Requires 1024 MB of memory --
	SelectMapOne
	LaunchRover
}
--run ComputePlan_MapOne for 9 Position, 1 Rover, 1 Path, 1 Map, 9 MapObject, 10 steps

/* Launch Rover in MapTwo */
pred ComputePlan_MapTwo {
	 -- Requires 1536 MB of memory --
	SelectMapTwo
	LaunchRover
}
run ComputePlan_MapTwo for 16 Position, 1 Rover, 1 Path, 1 Map, 6 MapObject, 20 steps

