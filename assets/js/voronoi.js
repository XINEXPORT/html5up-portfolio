// Voronoi Banner - Modified from original by @neave
// Adapted for fixed-size banner with purple color scheme

window.requestAnimationFrame =
	window.requestAnimationFrame ||
	window.webkitRequestAnimationFrame ||
	window.mozRequestAnimationFrame ||
	window.msRequestAnimationFrame ||
	function(callback) {
		setTimeout(callback, 1000 / 60);
	};

Array.prototype.each = function(f) {
	var i = this.length;
	while (i--) {
		f(this[i]);
	}
};

function Edge() {
	this.data = undefined;
	this.next = undefined;
	this.rot = undefined;
}

Edge.prototype.splice = function(e) {
	var e1 = this.next.rot,
		e2 = e.next.rot,
		e3 = this.next;

	this.next = e.next;
	e.next = e3;

	e3 = e1.next;
	e1.next = e2.next;
	e2.next = e3;
};

Edge.prototype.swap = function() {
	var e0 = this.oPrev(),
		e1 = this.sym().oPrev();

	this.splice(e0);
	this.sym().splice(e1);
	this.splice(e0.lNext());
	this.sym().splice(e1.lNext());
	this.setOrg(e0.dest());
	this.setDest(e1.dest());
};

Edge.prototype.sym = function() {
	return this.rot.rot;
};

Edge.prototype.iRot = function() {
	return this.rot.rot.rot;
};

Edge.prototype.org = function(v) {
	return this.data;
};

Edge.prototype.setOrg = function(v) {
	this.data = v;
};

Edge.prototype.dest = function() {
	return this.rot.rot.data;
};

Edge.prototype.setDest = function(v) {
	this.rot.rot.data = v;
};

Edge.prototype.setOrgDest = function(o, d) {
	this.setOrg(o);
	this.setDest(d);
};

Edge.prototype.left = function() {
	return this.rot.rot.rot.data;
};

Edge.prototype.setLeft = function(v) {
	this.rot.rot.rot.data = v;
};

Edge.prototype.right = function() {
	return this.rot.data;
};

Edge.prototype.setRight = function(v) {
	this.rot.data = v;
};

Edge.prototype.oNext = function() {
	return this.next;
};

Edge.prototype.rNext = function() {
	return this.rot.next.rot.rot.rot;
};

Edge.prototype.dNext = function() {
	return this.rot.rot.next.rot.rot;
};

Edge.prototype.lNext = function() {
	return this.rot.rot.rot.next.rot;
};

Edge.prototype.oPrev = function() {
	return this.rot.next.rot;
};

Edge.prototype.rPrev = function() {
	return this.rot.rot.next;
};

Edge.prototype.dPrev = function() {
	return this.rot.rot.rot.next.rot.rot.rot;
};

Edge.prototype.lPrev = function() {
	return this.next.rot.rot;
};

Edge.prototype.leftVertex = function(v) {
	return isLeftOf(v, this.org(), this.dest());
};

Edge.prototype.rightVertex = function(v) {
	return isRightOf(v, this.org(), this.dest());
};

Edge.prototype.colinearVertex = function(v) {
	return colinear(v, this.org(), this.dest());
};


function Vertex(x, y) {
	this.x = x;
	this.y = y;
	this.vx = 0;
	this.vy = 0;
	this.cell = 0;
	this.isInfinity = false;
}

Vertex.prototype.equals = function(v) {
	return this.x === v.x && this.y === v.y;
};


var canvas,
	context,
	scale,
	boundary = 25,
	totalVertices = 40,
	maxSpeed = 2,
	vertices = [],
	r,
	g,
	b,
	ri,
	gi,
	bi,
	rotMap = [1, 2, 3, 0],
	nextMap = [0, 3, 2, 1],
	edge,
	edges = [],
	circumcenters = [],
	edgeVertices = [new Vertex(0, -5000), new Vertex(-10000, 5000), new Vertex(10000, 5000)],
	maxIterations = 200,
	followDist = 300,
	stirDist = 100,
	mouseX,
	mouseY,
	oldMouseX = 0,
	oldMouseY = 0;

function inCircle(v0, v1, v2, v3) {
	var test = (v2.x - v1.x) * (v3.y - v1.y) * (v0.x * v0.x + v0.y * v0.y - v1.x * v1.x - v1.y * v1.y) +
		(v3.x - v1.x) * (v0.y - v1.y) * (v2.x * v2.x + v2.y * v2.y - v1.x * v1.x - v1.y * v1.y) +
		(v0.x - v1.x) * (v2.y - v1.y) * (v3.x * v3.x + v3.y * v3.y - v1.x * v1.x - v1.y * v1.y) -
		(v2.x - v1.x) * (v0.y - v1.y) * (v3.x * v3.x + v3.y * v3.y - v1.x * v1.x - v1.y * v1.y) -
		(v3.x - v1.x) * (v2.y - v1.y) * (v0.x * v0.x + v0.y * v0.y - v1.x * v1.x - v1.y * v1.y) -
		(v0.x - v1.x) * (v3.y - v1.y) * (v2.x * v2.x + v2.y * v2.y - v1.x * v1.x - v1.y * v1.y);

	return test >= 0;
}

function area(v0, v1, v2) {
	return (v1.x - v0.x) * (v2.y - v0.y) - (v2.x - v0.x) * (v1.y - v0.y);
}

function distSq(v0, v1) {
	return (v1.x - v0.x) * (v1.x - v0.x) + (v1.y - v0.y) * (v1.y - v0.y);
}

function colinear(v0, v1, v2) {
	return area(v1, v0, v2) === 0;
}

function isRightOf(v0, v1, v2) {
	return area(v0, v1, v2) > 0;
}

function isLeftOf(v0, v1, v2) {
	return area(v0, v1, v2) < 0;
}

function getQuadEdge() {
	var e = [new Edge(), new Edge(), new Edge(), new Edge()],
		i;

	for (i = 0; i < 4; i++) {
		e[i].rot = e[rotMap[i]];
		e[i].next = e[nextMap[i]];
	}

	return e[0];
}

function deleteQuadEdge(e) {
	disconnect(e);
	[e, e.rot, e.sym(), e.iRot()].each(function(q) {
		delete q;
	});
}

function initDelaunay() {
	edges.each(function(e) {
		deleteQuadEdge(e);
	});
	edges = [];
	circumcenters = [];

	edgeVertices.each(function(v) {
		v.isInfinity = true;
	});

	edges[0] = getQuadEdge();
	edges[2] = getQuadEdge();
	edges[0].setOrgDest(edgeVertices[1], edgeVertices[2]);
	edges[2].setOrgDest(edgeVertices[1], edgeVertices[0]);
	edges[0].splice(edges[2]);
	edges[2] = edges[2].sym();
	edges[1] = connect(edges[0], edges[2]);
	edge = edges[0];
}

function inCosmic(v) {
	var cosmic = true;
	[edges[0], edges[1], edges[2]].each(function(e) {
		cosmic &= e.leftVertex(v);
	});
	return cosmic;
}

function locate(v) {
	if (edge.rightVertex(v)) {
		edge = edge.sym();
	}

	var i = 0;
	while (i++ < maxIterations && !v.equals(edge.org()) && !v.equals(edge.dest())) {
		if (!edge.oNext().rightVertex(v)) {
			edge = edge.oNext();
		} else if (!edge.dPrev().rightVertex(v)) {
			edge = edge.dPrev();
		} else {
			return edge;
		}
	}
}

function connect(e0, e1) {
	var e2 = getQuadEdge();
	e2.setOrgDest(e0.dest(), e1.org());
	e2.splice(e0.lNext());
	e2.sym().splice(e1);
	return e2;
}

function disconnect(e) {
	e.splice(e.oPrev());
	e.sym().splice(e.sym().oPrev());
}

function circumcenter(v0, v1, v2) {
	var denominator = (v1.y - v2.y) * (v1.x - v0.x) - (v1.y - v0.y) * (v1.x - v2.x),
		num0 = ((v0.x + v1.x) * (v1.x - v0.x)) / 2 + ((v1.y - v0.y) * (v0.y + v1.y)) / 2,
		num1 = ((v1.x + v2.x) * (v1.x - v2.x)) / 2 + ((v1.y - v2.y) * (v1.y + v2.y)) / 2,
		c = new Vertex((num0 * (v1.y - v2.y) - num1 * (v1.y - v0.y)) / denominator, (num1 * (v1.x - v0.x) - num0 * (v1.x - v2.x)) / denominator);

	circumcenters.push(c);
	return c;
}

function setCircumcenter(e) {
	var cc = circumcenter(e.dest(), e.org(), e.oNext().dest());
	circumcenters.push(cc);
	e.setLeft(cc);
	e.lNext().setLeft(cc);
	e.lPrev().setLeft(cc);
}

function insert(vertex) {
	if (!inCosmic(vertex)) {
		return;
	}

	var e = locate(vertex);
	if (!e) {
		return;
	}

	if (edge.colinearVertex(vertex)) {
		e = edge.oPrev();
		disconnect(edge);
		deleteQuadEdge(edge);
		edge = e;
	}
	e = getQuadEdge();

	var v = edge.org();

	edges.push(e);
	e.setOrgDest(v, vertex);
	e.splice(edge);

	do {
		e = connect(edge, e.sym());
		edges.push(e);
		edge = e.oPrev();
	} while (edge.dest() !== v);

	while (true) {
		e = edge.oPrev();
		if (edge.rightVertex(e.dest()) && inCircle(vertex, edge.org(), e.dest(), edge.dest())) {
			edge.swap();
			setCircumcenter(edge);
			edge = edge.oPrev();
		} else {
			if (edge.org() === v) {
				setCircumcenter(edge);
				return;
			}
			setCircumcenter(edge);
			edge = edge.oNext().lPrev();
		}
	}
}

function clamp(value, lower, upper) {
	return value < lower ? lower : value > upper ? upper : value;
}

function randomizeColorInc() {
	ri = Math.random() * 0.3 + 0.2;
	gi = Math.random() * 0.2 + 0.1;
	bi = Math.random() * 0.4 + 0.3;
}

function randomizeColors() {
	// Purple color scheme - bias toward purple hues
	r = 180 + Math.random() * 40;  // 180-220 range
	g = 120 + Math.random() * 40;  // 120-160 range
	b = 200 + Math.random() * 40;  // 200-240 range
}

function getColor(cell) {
	var cr = Math.floor(cell * 0.5 + r),
		cg = Math.floor(cell * 0.3 + g),
		cb = Math.floor(cell * 0.6 + b);

	cr %= 255;
	cg %= 255;
	cb %= 255;

	// Ensure purple tones
	cr = Math.max(cr, 140);
	cg = Math.max(cg, 100);
	cb = Math.max(cb, 180);

	return 'rgb(' + cr.toString() + ',' +  cg.toString() + ',' + cb.toString() + ')';
}

function drawTriangle(v0, v1, v2, color) {
	context.fillStyle = color;
	context.beginPath();
	context.moveTo(v0.x, v0.y);
	context.lineTo(v1.x, v1.y);
	context.lineTo(v2.x, v2.y);
	context.lineTo(v0.x, v0.y);
	context.closePath();
	context.fill();
}

function draw() {
	var vertex,
		x,
		y,
		vx,
		vy,
		absVX,
		absVY,
		dx,
		dy,
		d,
		angle,
		ca,
		sa,
		a,
		i = totalVertices;

	if (oldMouseX === undefined) {
		oldMouseX = mouseX;
	}
	if (oldMouseY === undefined) {
		oldMouseY = mouseY;
	}
	mouseVX = mouseX - oldMouseX;
	mouseVY = mouseY - oldMouseY;
	oldMouseX = mouseX;
	oldMouseY = mouseY;

	initDelaunay();

	while (i--) {
		vertex = vertices[i];
		x = vertex.x;
		y = vertex.y;
		vx = vertex.vx;
		vy = vertex.vy;
		dx = x - mouseX;
		dy = y - mouseY;
		d = Math.sqrt(dx * dx + dy * dy);
		angle = Math.atan2(dy, dx);
		ca = Math.cos(angle);
		sa = Math.sin(angle);

		if (d < followDist) {
			a = (1 - (d / followDist)) * canvas.width * 0.001;
			vx -= ca * (a + Math.random() * 8 - 4);
			vy -= sa * (a + Math.random() * 8 - 4);
		}

		if (d < stirDist) {
			a = (1 - (d / stirDist)) * canvas.width * 0.0005;
			vx += mouseVX * a;
			vy += mouseVY * a;
		}

		absVX = Math.abs(vx);
		absVY = Math.abs(vy);

		if (absVX < 0.1) {
			vx *= Math.random() * maxSpeed;
		} else if (absVX > maxSpeed) {
			vx *= 0.9;
		}

		if (absVY < 0.1) {
			vy *= Math.random() * maxSpeed;
		} else if (absVY > maxSpeed) {
			vy *= 0.9;
		}

		var nextX = x + vx,
			nextY = y + vy;

		if (nextX > canvas.width) {
			nextX = canvas.width;
			vx *= -1;
		} else if (nextX < 0) {
			nextX = 0;
			vx *= -1;
		}

		if (nextY > canvas.height) {
			nextY = canvas.height;
			vy *= -1;
		} else if (nextY < 0) {
			nextY = 0;
			vy *= -1;
		}

		if (!vx) {
			vx = 0;
		}
		if (!vy) {
			vy = 0;
		}

		vertex.vx = vx;
		vertex.vy = vy;
		vertex.x = nextX;
		vertex.y = nextY;
		vertex.cell = i;
		insert(vertex);
	}

	// Update colors
	if (b < 3) {
		randomizeColorInc();
	}
	r += ri;
	g += gi;
	b += bi;

	edges.each(function(edge) {
		var org = edge.org(),
			dest = edge.dest(),
			left = edge.left(),
			right = edge.right();

		if (!org.isInfinity && right && left) {
			drawTriangle(org, right, left, getColor(org.cell));
		}

		if (!dest.isInfinity && right && left) {
			drawTriangle(dest, left, right, getColor(dest.cell));
		}
	});
}

function resize() {
	scale = 1;

	// Use banner container dimensions instead of window
	var container = canvas.parentElement;
	canvas.width = container.offsetWidth * scale;
	canvas.height = container.offsetHeight * scale;
	canvas.style.width = container.offsetWidth + 'px';
	canvas.style.height = container.offsetHeight + 'px';

	vertices = [];
	// Adjusted for smaller banner area
	totalVertices = Math.max(30, Math.round(canvas.width * canvas.height / 15000));
	for (var i = totalVertices; i--; ) {
		var vertex = new Vertex(canvas.width * Math.random(), canvas.height * Math.random());
		vertex.vx = Math.cos(i) * Math.random() * maxSpeed;
		vertex.vy = Math.sin(i) * Math.random() * maxSpeed;
		vertices.push(vertex);
	}

	draw();
}

function update() {
	requestAnimationFrame(update);
	draw();
}

function init() {
	canvas = document.getElementById('voronoi-canvas');
	if (!canvas) {
		console.error('Voronoi canvas not found');
		return;
	}
	
	context = canvas.getContext('2d');

	canvas.ontouchmove = canvas.ontouchstart = function(event) {
		var rect = canvas.getBoundingClientRect();
		mouseX = (event.targetTouches[0].pageX - rect.left) * scale;
		mouseY = (event.targetTouches[0].pageY - rect.top) * scale;
		followDist = 800;
		event.preventDefault();
	};

	canvas.ontouchend = function(event) {
		mouseX = mouseY = undefined;
		followDist = 300;
		for (var i = totalVertices; i--; ) {
			var vertex = vertices[i];
			vertex.vx += (Math.random() - 0.5) * 50;
			vertex.vy += (Math.random() - 0.5) * 50;
		}
		randomizeColors();
		randomizeColorInc();
	};

	canvas.onmousemove = function(event) {
		var rect = canvas.getBoundingClientRect();
		mouseX = (event.pageX - rect.left) * scale;
		mouseY = (event.pageY - rect.top) * scale;
	};

	canvas.onmouseout = canvas.onmouseleave = function() {
		mouseX = mouseY = undefined;
	};

	canvas.onmousedown = function() {
		followDist = 800;
	};

	canvas.onmouseup = function() {
		mouseX = mouseY = undefined;
		followDist = 300;
		for (var i = totalVertices; i--; ) {
			var vertex = vertices[i];
			vertex.vx += (Math.random() - 0.5) * 100;
			vertex.vy += (Math.random() - 0.5) * 100;
		}
		randomizeColors();
		randomizeColorInc();
	};

	randomizeColors();
	randomizeColorInc();

	window.onresize = resize;

	resize();
	update();
}

document.addEventListener('DOMContentLoaded', init);
