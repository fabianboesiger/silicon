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

    /* STAGE 1: Extract all necessary information about the annotated code */

    // Get class declaration and companion object declaration if it exists.
    val (classDecl, companionDecl) = inputs match {
      case (head: ClassDef) :: Nil => (head, None)
      case (head: ClassDef) :: (tail: ModuleDef) :: Nil => (head, Some(tail))
      case _ => c.abort(c.enclosingPosition, "Annotation is only allowed on classes with optional companion object.")
    }

    // Extract information from class declaration.
    val (className, fields, bases, body) = try {
      val q"case class $className $_(..$fields) extends ..$bases { ..$body }" = classDecl
      // TODO: Assert that class implements Term trait.
      (className, fields, bases, body)
    } catch {
      case _: MatchError => c.abort(c.enclosingPosition, "Could not parse class, is it a case class?")
    }

    // Get definitions from companion object, if any.
    // They are later inserted into the newly generated companion object.
    val companionDefns = companionDecl match {
      case Some(companionDecl) =>
        val q"object $_ extends ..$_ { ..$companionBody }" = companionDecl
        companionBody
      case None => List(q"")
    }

    /* STAGE 2: Preparation, check what methods already are defined, rename apply to _apply. */

    // Some helper values.
    val fieldTypes = fields.map(_.tpt).toList
    val fieldNames = fields.map(_.name).toList
    val termName = TermName(className.toString) // TODO: This seems wrong, but it works for now.

    // TODO: Find a better solution.
    // Check if an apply method already exists and rename it.
    var hasRenamedApplyMethod = false
    var hasUnapplyMethod = false
    var returnType = className
    val renamedCompanionDefns = companionDefns
      .map((elem) => try {
        val defn = elem.asInstanceOf[DefDef]
        val q"$_ def $methodName(...${methodFields}): $methodReturnType = $methodBody" = defn

        if (methodName.toString == "unapply") hasUnapplyMethod = true

        if (methodName.toString == "apply" && methodFields.head.length == fields.length && methodFields.head
          .zip(fields)
          .map({ case (mf, f) => mf.tpt.toString == f.tpt.toString })
          .foldLeft(true)(_ && _)
        ) {
          hasRenamedApplyMethod = true
          // TODO: Make it possible to use implicit return type. (Using context?)
          if (methodReturnType.toString == "<type ?>")
            c.abort(c.enclosingPosition, "Return type of non-compiler-generated apply method has to be explicit.")
          else
            returnType = TypeName(methodReturnType.toString)
          q"private def _apply (...${methodFields}): $methodReturnType = $methodBody"
        } else defn
      } catch {
        case _: ClassCastException => elem
      })

    /* STAGE 3: Generate output. */

    // Create output from the extracted information.
    q"""
      class $className private[terms] (..$fields) extends ..$bases { ..$body }

      object ${termName} extends ((..${fieldTypes}) => $returnType) {
        import scala.collection.mutable.HashMap
        var pool = new HashMap[(..${fieldTypes}), $returnType]

          def apply(..$fields) = {
            pool.get((..${fieldNames})) match {
              case Some(term) => term
              case None =>
                val term = ${
                  // Use the now renamed apply method to create an instance of this object.
                  if (hasRenamedApplyMethod)
                    q"${termName}._apply(..${fieldNames})"
                  else
                    q"new $className(..${fieldNames})"
                }
                pool.addOne(((..${fieldNames}), term))
                term
            }
          }

        ${ // Create unapply method only if not already defined.
          if (!hasUnapplyMethod)
            q"""def unapply(t: $className) = {
              ${
                // Turns out unapply on case classes without fields return true instead of an Option.
                if (fields.isEmpty)
                  q"true"
                else
                  q"Some((..${fieldNames.map(name => q"t.$name").toList}))"
              }
            }"""
          else q""
        }

        ..$renamedCompanionDefns
      }
    """
  }
}
/*

*/