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

    // Extract information from class declaration.
    val q"""
      case class $className (..$fields) extends ..$bases { ..$body }
    """ = classDecl

    // Create output tree.
    val output = q"""
      class $className private (..$fields) extends ..$bases { ..$body }

      object ${TermName(className.toString)} extends ((Term, Term) => Term) {
        def apply(..$fields) = {
          new $className(..${fields.map(_.name).toList})
        }

        def unapply(t: $className) = {
          Some((..${fields.map(_.name).map(name => q"t.$name").toList}))
        }
      }
    """

    println(output)

    output
  }
}