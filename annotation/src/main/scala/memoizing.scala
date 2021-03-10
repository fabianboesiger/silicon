package viper.silicon.annotation

import scala.annotation.{StaticAnnotation, compileTimeOnly}
import scala.language.experimental.macros
import scala.reflect.macros.whitebox

@compileTimeOnly("Could not expand macro.")
class memoizing extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro memoizingMacro.impl
}

object memoizingMacro {
  def impl(c: whitebox.Context)(annottees: c.Expr[Any]*) = {
    import c.universe._
    val inputs = annottees.map(_.tree).toList

    // Get class declaration and companion object declaration if it exists.
    val (classDecl, companionDecl) = inputs match {
      case (head: ClassDef) :: Nil => (head, None)
      case (head: ClassDef) :: (tail: ModuleDef) :: Nil => (head, Some(tail))
      case _ => c.abort(c.enclosingPosition, "Annotation is only allowed on classes with optional companion object.")
    }

    // Extract information from class declaration.
    val (className, fields, bases, body) = try {
      val q"case class $className (..$fields) extends ..$bases { ..$body }" = classDecl
      // TODO: Assert that class implements Term trait.
      (className, fields, bases, body)
    } catch {
      case _: MatchError => c.abort(c.enclosingPosition, "Could not parse class, is it a case class?")
    }

    // Get definitions from companion object, if any.
    // They are later inserted into the newly generated companion object.
    val companionDefns = companionDecl match {
      case Some(companionDecl) =>
        val q"object $companionName extends ..$companionBases { ..$companionBody }" = companionDecl
        companionBody
      case None => List(q"")
    }

    // Some helper values.
    val fieldTypes = fields.map(_.tpt).toList
    val fieldNames = fields.map(_.name).toList

    // Create output from the extracted information.
    val output = q"""
      class $className private (..$fields) extends ..$bases { ..$body }

      object ${TermName(className.toString)} extends ((..${fieldTypes}) => $className) {
        import scala.collection.mutable.HashMap
        var pool = new HashMap[(..${fieldTypes}), $className]

          def apply(..$fields) = {
            pool.get((..${fieldNames})) match {
              case Some(term) => term
              case None =>
                val term = new $className(..${fieldNames})
                pool.addOne(((..${fieldNames}), term))
                term
            }
          }

        def unapply(t: $className) = {
          ${
            // Turns out unapply on case classes without fields return true instead of an Option.
            if (fields.isEmpty)
              q"true"
            else
              q"Some((..${fieldNames.map(name => q"t.$name").toList}))"
          }
        }

        ..$companionDefns
      }
    """

    //println(output)

    output
  }
}
/*

*/