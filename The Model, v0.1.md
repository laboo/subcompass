# The Model, v0.1

We are going to build a universe with geometry. Standard Euclidean geometry, mostly, but each object will have a container. Each geometrical point lives inside the very same point container, which we will refer to as the origin. The origin constitutes a zero-dimensional (0D) world, and like all our containers, it can contain an infinite number of points. At the start, it holds a loose bag of them, nothing yet bound. Every 0D point has one of two values, 1 or -1, which you should think of as (+1)⁰ and (-1)⁰, and which we will refer to as the symbols: ⊕ and ⊖. Their names are positive (⊕) and negative (⊖). The anti-matter twin of any object is that same object with every ⊕ and ⊖ flipped.

The 1D container/world is a line, like a perfectly straight (and conceptually infinitely long) tube, that contains points. These points are 1D points (+1)¹ and (-1)¹, which we will refer to as the symbols [+] and [−], making each a line segment, the smallest unit of the 1D world, made of two 0D points, each marking one end of the line segment.

These are all of the things that exist in 1D.

((+1)⁰ × (+1)⁰) and swapped, ((+1)⁰ × (+1)⁰) (identical twins switching places)

((-1)⁰ × (-1)⁰) and swapped, ((-1)⁰ × (-1)⁰)

((+1)⁰ × (-1)⁰) and swapped, ((-1)⁰ × (+1)⁰)

Order counts, so each line above is two different things, even the first two lines, where the swap looks exactly the same on the page, like identical twins who have switched places. That is because every point is an individual: two ⊕ have the same value, but they are still two points.

They exist because they are made only of 0D points, (+1)⁰ and (−1)⁰, bound together by multiplication, which carries things from one dimension into the next (addition, as we’ll see later, joins things within a dimension).

| New Symbol | Things That Exist in 1D | Nicknames for them |
| --- | --- | --- |
| [+] | ((+1)⁰ × (+1)⁰) and ((-1)⁰ × (-1)⁰) | (+1)¹ and (⊕ × ⊕) and (⊖ × ⊖) |
| [-] | ((+1)⁰ × (-1)⁰) and ((-1)⁰ × (+1)⁰) | (-1)¹ and (⊖ × ⊕) and (⊕ × ⊖) |

Note the mismatch between the number of points inside each thing and the number of dimensions it lives in: two points inside, one dimension outside. In general, a thing in n dimensions is made of n + 1 points.

Multiplication keeps going the same way. Binding a thing to one more point from the bag carries it into the next dimension, and the new point goes last in its order: a segment and one more point make a triangle, three points in 2D; a triangle and one more point make a tetrahedron, four points in 3D; and so on, with no top. A point belongs to at most one thing, and a point bound to nothing is a 0D point in the bag.

A thing’s value is the product of its points, just as in the 1D table: (+1)ⁿ or (−1)ⁿ for an n-dimensional thing. A thing’s hand is its order: its mirror image is the same points with two of them swapped. Nothing else records which side a point was bound on.

There is a container for every dimension: the origin (0D), the line (1D), the plane (2D), space (3D), and so on, with no top. A thing of n + 1 points lives in the n-dimensional container, and every point bound to nothing sits at the origin. Inside a container, the model keeps track of only one thing: which points are at the same place. Positions and distances never enter it.

Addition (+) brings points of different things in the same container to one place. Any number of pairs can be brought together at once, as when one thing is laid on another. A place keeps every point brought to it, with no order among them; their sum is only the flattened view. Bringing a point to a place brings everything already there, and points brought together stay together unless they come apart or their thing changes container. Addition never brings together two points of the same thing, or things of different dimensions, and never reaches the bag.

Right after every event, every place holding both a ⊕ and a ⊖ comes apart: all the points there come unbound at once and go back to the bag. A thing that loses points keeps the rest, in their order, and drops one dimension for each point lost; a thing left with a single point dissolves into the bag. Places holding only like points, (⊕ + ⊕) or (⊖ + ⊖), don’t come apart. One round always finishes the job: afterwards, no place holds both a ⊕ and a ⊖.

A thing that changes container, by gaining a point through × or by losing points as it comes apart, arrives in its new container touching nothing.

Only × and + ever happen, one at a time, in whatever order a setup chooses. Nothing happens by itself, and there is no clock, only the order of events. An event can happen exactly when it names only points the world has, and what it does, before anything comes apart, leaves a world in which:

- every thing has at least two points;
- a point belongs to at most one thing, and appears in it once;
- every place holds at least two points, all of them bound;
- a point is at one place at most;
- a thing’s own points are never at the same place;
- everything at a place has the same dimension.

A world holds as many points as a setup wants, finitely many at any moment, and its points never change: events only bind, join and unbind them.

Without changing anything, one can read off a world: which points are in the bag, each thing’s points in order, dimension and value, the sum of any points, and what an event releases, the points that came apart together at each place, such as a (⊕ + ⊖) pair. No rule uses these readings.
