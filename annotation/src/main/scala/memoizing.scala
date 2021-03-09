package viper.silicon.annotation

import scala.annotation.{StaticAnnotation, compileTimeOnly}
import scala.language.experimental.macros
import scala.reflect.macros.whitebox

@compileTimeOnly("Could not expand macro")
class memoizing extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro memoizingMacro.impl
}


object memoizingMacro {
  def impl(c: whitebox.Context)(annottees: c.Expr[Any]*) = {
    import c.universe._
    val inputs = annottees.map(_.tree).toList

    println(inputs.map(_.getClass).toList)

    // Get class declaration and companion objects if they exist.
    val (classDecl, companionObj) = inputs match {
      case (head: ClassDef) :: Nil => (head, Nil)
      case (head: ClassDef) :: (tail @ (_ :: _)) => (head, tail)
      case _ => c.abort(c.enclosingPosition, "Annotation is only supported on case classes")
    }

    println((classDecl, companionObj))

    /*
    // Get case class name and fields.
    val (className, fields) = try {
      val q"case class $className(..$fields) extends ..$bases { ..$body }" = classDecl
      (className, fields)
    } catch {
      case e: MatchError => c.abort(c.enclosingPosition, "Annotation is only supported on case classes")
    }

    println((className, fields))

    val fieldData = fields.map(field => try {
      //val q"val $fieldName: $fieldType = $fieldInit" = field
      (field.name, field.tpt, field.rhs)
    } catch {
      case e: MatchError => c.abort(c.enclosingPosition, e.toString())
    }).toList

    println(fieldData)
    */

    val q"case class $className(..$fields) extends ..$bases { ..$body }" = classDecl

    q"""
      class $className private (..$fields) extends ..$bases { ..$body }

      object ${TermName(className.toString)} extends ((Term, Term) => $className) {
        def apply(..$fields) = {
          new $className(..${fields.map(_.name).toList})
        }
      }
    """
  }
}