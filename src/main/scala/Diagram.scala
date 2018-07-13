package fir2dot

import java.io.{BufferedWriter, File, FileWriter, PrintWriter}

import firrtl.{CircuitState, Transform, UnknownForm}
import firrtl.ir._
import firrtl.passes.Pass

import scala.collection.mutable

object Diagram extends Pass {
	override def name = "Diagram"

	def dumpLoc(loc: Expression, acc: String): String = {
		loc match {
			case r: Reference => r.name + acc
			case s: SubField => dumpLoc(s.expr, acc) + "." + s.name
			case i: SubIndex => dumpLoc(i.expr, acc) + "[" + i.value + "]"
			case s => acc
		}
	}

	def dumpConnect(m: DefModule)(c: Connect): Unit = {
		if (connections contains m.name) {
			connections(m.name) = connections(m.name) :+ (dumpLoc(c.loc, ""), dumpLoc(c.expr, ""))
		} else {
			connections(m.name) = Seq((dumpLoc(c.loc, ""), dumpLoc(c.expr, "")))
		}
	}

	def dumpStmts(m: DefModule)(s: Statement): Statement = {
		s match {
			case s: Connect => dumpConnect(m)(s)
			case s: DefInstance => {
				if (hierarchy contains m.name) {
					hierarchy(m.name) = hierarchy(m.name) :+ (s.module, s.name)
				} else {
					hierarchy(m.name) = Seq((s.module, s.name))
				}

			}
			case s => {
				s mapStmt dumpStmts(m)
			}
		}
		s
	}

	def dumpPorts(context: PrintWriter)(module: String)(p: Port): Port = {
		context.write(p.name)
		p
	}

	def getField(f: Field, acc: String): String = {
		getType(f.tpe, acc + "." + f.name)
	}

	def getType(t: Type, acc: String): String = {
		t match {
			case b: BundleType => {
				(b.fields map (f => getField(f, acc))).mkString("|")
			}
			case c: UIntType => {
				acc
			}
			case v: VectorType => {
				(for (i <- 0 until v.size) yield getType(v.tpe, acc + "[" + i + "]")).mkString("|")
			}
			case b: Type => acc
		}
	}


	def getPortName(p: Port): String = {
		getType(p.tpe, p.name)
	}

	def dumpModule(m: DefModule): Unit = {
		m mapStmt dumpStmts(m)
		val names = (m.ports map (p => getPortName(p))).mkString("|")
		// ugly hack
		portList(m.name) = names.split("\\|")
	}

	val hierarchy: mutable.Map[String, Seq[(String, String)]] = mutable.HashMap.empty[String, Seq[(String, String)]]
	val portList: mutable.Map[String, Seq[String]] = mutable.HashMap.empty[String, Seq[String]]
	val connections: mutable.Map[String, Seq[(String, String)]] = mutable.HashMap.empty[String, Seq[(String, String)]]

	def sanitize(s: String): String = {
		s.replace(".", "_").replace("[", "_").replace("]", "")
	}

	def isMultiPort(l: Seq[String], k: String): Boolean = {
		val portpins = l.filter(s => s.startsWith(k+"."))
		if( portpins.length != 0 ) { for ( portpin <- portpins ) {
			var ppar = portpin.split(k+"\\.", 2)
			if( ppar.length ==2 ) {
				var ppn = ppar(1).split("\\.", 2)
				if( ppn.length == 2 ) return true;
			}
		}}
		return false
	}
	
	def getSubPins(p: Seq[String], l: Seq[String], k: String): Seq[String] = {
		var ret = Array[String] ()
		var ios = (l.filter(s => s.startsWith(k+".")))
		var fil = k.replace("[", "_").replace("]", "")
		for ( io <- ios ) {
			var newIO = io.replace("[", "_").replace("]", "")
			var ioar = newIO.split(fil+"\\.", 2)
			if( ioar.length > 1 ) {
				var fullPathArray = p ++ Array(ioar(1))
				var rs = sanitize(ioar(1))
				//rs = rs + "<"
				//rs = rs + sanitize(fullPathArray.mkString("_"))
				//rs = rs + ">"
				ret = Array(rs) ++ ret
			} else {
				println(ioar)
			}
		}
		return ret
	}

	def getPortGraphString(p: Seq[String], l: Seq[String]) : String = {
		var ret=""
		var subgraphs = Array[String] ()
		var ports = Array[String] ()
		for ( iopin <- l ) {
			var keys = iopin.split("\\.", 2)
			if(keys(0)!="") {
				/*if(isMultiPort(l,keys(0))) {
					if( !( subgraphs contains keys(0) ) ) subgraphs = Array(keys(0)) ++ subgraphs
				} else if(keys.length==1) {
					var fullPathArray = p ++ Array(keys(0))
					ret=ret+"node_"+sanitize(fullPathArray.mkString("_"))+" [shape=box, label=\""
					ret=ret+sanitize(keys(0))
					ret=ret+"\"];\n"
				} else  {
					if( !( ports contains keys(0) ) ) ports = Array(keys(0)) ++ ports
				}*/
				if(keys.length==1) {
					var fullPathArray = p ++ Array(keys(0))
					ret=ret+"node_"+sanitize(fullPathArray.mkString("_"))+" [shape=box, label=\""
					ret=ret+sanitize(keys(0))
					ret=ret+"\"];\n"
				} else if(isMultiPort(l,keys(0))) {
					if( !( subgraphs contains keys(0) ) ) subgraphs = Array(keys(0)) ++ subgraphs
				}
			}
		}
		for ( portname <- ports ) {
			var ios = getSubPins(p, l, portname)
			var fullPathArray = p ++ Array(portname)
			ret=ret+"node_"+sanitize(fullPathArray.mkString("_"))+" [shape=record, label=\""+sanitize(portname)+"|{"+ios.mkString("|")+"}\"];\n"
		}
		for ( subgraph <- subgraphs ) {
			var ios = (l.filter(s => s.startsWith(subgraph+"."))) map (port => port.split(subgraph+"\\.", 2)(1))
			ret=ret+"subgraph cluster_"+sanitize(subgraph)+" {\n"
			ret=ret+"graph[style=dotted];\n"
			ret=ret+"color=blue;\n"
			ret=ret+"label=\""+sanitize(subgraph)+"\";\n"
			ret=ret+getPortGraphString(p++Array(subgraph), ios)
			ret=ret+"}\n"
		}
		ret
	}

	def getConnectionLeaf(l: String) : String = {
		var ar = l.split("\\.", 2)
		if ( ar.length == 2 ) {
			return "_"+sanitize(ar(0))+getConnectionLeaf(ar(1))
		} else {
			return ":"+sanitize(ar(0))
		}
	}

	override def run(c: Circuit): Circuit = {
		c.modules foreach dumpModule
		for (m <- hierarchy.keys) {
			if(m!="PlusArgTimeout") {
				val context: PrintWriter = new PrintWriter(new File(m+".dot"))
				context.write("digraph G{\n")
				context.write("subgraph cluster_"+sanitize(m)+" {\n")
				context.write("graph [style=dotted, rankdir=LR];\n")
				context.write("label=\""+sanitize(m)+"\";\n")
				context.write(getPortGraphString(Array(m), portList(m))) // io ports
				// sub modules
				for (submodule <- hierarchy(m)) {
					context.write("subgraph cluster_"+sanitize(submodule._2)+"{\n")
					context.write("graph [style=dotted, rankdir=LR];\n")
					context.write("label=\""+sanitize(submodule._2)+"\";\n")
					context.write(getPortGraphString(Array(m)++Array(submodule._2), portList(submodule._1)))
					context.write("}\n")
				}
				// connections
				for ((what, where) <- connections(m)) {
					var toIsOK: Boolean = false
					var fromIsOK: Boolean = false
					val toModuleName = where.split("\\.", 2)(0)
					val fromModuleName = what.split("\\.", 2)(0)
					var from = "logic"
					var to = "logic"
					if (toModuleName == "clock" || toModuleName == "reset" || toModuleName == "io" || hierarchy(m).exists(item => {
						item._2 == toModuleName
					})) {
						toIsOK = true
					}
					if (fromModuleName == "clock" || fromModuleName == "reset" || fromModuleName == "io" || hierarchy(m).exists(item => {
						item._2 == fromModuleName
					})) {
						fromIsOK = true
					}
					if (fromIsOK) {
						from = "node_"+m+getConnectionLeaf(what)
					}
					if (toIsOK) {
						to = "node_"+m+getConnectionLeaf(where)
					}
					if(from!=to) {
						if ( (toModuleName == "clock") || ( fromModuleName == "clock" ) ) {
							context.write("edge [dir=none, color=green]")
						} else if ( (toModuleName == "reset") || ( fromModuleName == "reset" ) ) {
							context.write("edge [dir=none, color=red]")
						} else {
							context.write("edge [dir=none, color=black]")
						}
						context.write(from + " -> " + to + ";\n")
					}
				}
				context.write("}\n")
				context.write("}\n")
				context.flush()
				context.close()
			}
		}
		c
	}
}

object Main extends App {
	if (args.length != 1) {
		println("Usage: diagram fir_file")
	} else {
		val input: String = scala.io.Source.fromFile(args(0)).mkString
		val state = CircuitState(firrtl.Parser.parse(input), UnknownForm)
		val transforms = Seq(Diagram)
		transforms.foldLeft(state) {
			(c: CircuitState, t: Transform) => t.runTransform(c)
		}
	}
}
