package kuplrg

object Implementation extends Template {

  import Expr.*, RecDef.*, Value.*, Type.*, TypeInfo.*

  def subst(ty: Type, mapping: Map[String, Type]): Type = ty match {
    case NothingT | AnyT | UnitT | NumT | BoolT | StrT => ty
    case IdT(name, tys) =>
      if (mapping.contains(name) && tys.isEmpty) mapping(name)
      else IdT(name, tys.map(subst(_, mapping)))
    case ArrowT(tvars, paramTys, retTy) =>
      val newMapping = mapping -- tvars
      ArrowT(tvars, paramTys.map(subst(_, newMapping)), subst(retTy, newMapping))
  }

  def subtype(t1: Type, t2: Type): Boolean = (t1, t2) match {
    case (_, AnyT) => true
    case (NothingT, _) => true
    case (t1, t2) if t1 == t2 => true
    
    case (IdT(n1, args1), IdT(n2, args2)) =>
      n1 == n2 && args1.length == args2.length && args1.zip(args2).forall { case (a, b) => subtype(a, b) }
    case (ArrowT(tv1, p1, r1), ArrowT(tv2, p2, r2)) =>
      if (tv1.length != tv2.length) false
      else {
        val mapping = tv1.zip(tv2.map(id => IdT(id))).toMap
        val p1Subst = p1.map(subst(_, mapping))
        val r1Subst = subst(r1, mapping)
        
        p1Subst.length == p2.length &&
        p1Subst.zip(p2).forall { case (a, b) => subtype(b, a) } &&
        subtype(r1Subst, r2)
      }
    case _ => false
  }

  def join(t1: Type, t2: Type): Type = {
    if (subtype(t2, t1)) t1
    else if (subtype(t1, t2)) t2
    else (t1, t2) match {
      case (IdT(n1, args1), IdT(n2, args2)) if n1 == n2 && args1.length == args2.length =>
        IdT(n1, args1.zip(args2).map { case (a, b) => join(a, b) })
      
      case (ArrowT(tv1, p1, r1), ArrowT(tv2, p2, r2)) if tv1.length == tv2.length && p1.length == p2.length =>
        val mapping = tv2.zip(tv1.map(id => IdT(id))).toMap
        val p2Subst = p2.map(subst(_, mapping))
        val r2Subst = subst(r2, mapping)
        
        val argsMeet = p1.zip(p2Subst).map { case (a, b) => 
           if (subtype(a, b)) a else if (subtype(b, a)) b else NothingT 
        }
        ArrowT(tv1, argsMeet, join(r1, r2Subst))

      case _ => AnyT
    }
  }

  def checkValidType(ty: Type, tenv: TypeEnv): Unit = ty match {
    case AnyT | NothingT | UnitT | NumT | BoolT | StrT => ()
    case IdT(name, args) =>
      val info = tenv.tys.getOrElse(name, error("Unknown type"))
      info match {
        case TIVar =>
          if (args.nonEmpty) error("keyword type cannot have arguments")
        case TIAdt(tvars, _) =>
          if (args.length != tvars.length) error("length not right?")
          args.foreach(checkValidType(_, tenv))
      }
    case ArrowT(tvars, paramTys, retTy) =>
      tvars.foreach { tv =>
        if (tenv.tys.contains(tv)) error("shadowing something worng...why...")
      }
      val newEnv = tenv.addTypeVars(tvars)
      paramTys.foreach(checkValidType(_, newEnv))
      checkValidType(retTy, newEnv)
  }

  def typeCheck(expr: Expr, tenv: TypeEnv): Type = expr match {
    case EUnit => UnitT
    case ENum(_) => NumT
    case EBool(_) => BoolT
    case EStr(_) => StrT
    
    case EId(name) => 
      tenv.vars.getOrElse(name, error("Unbound variable"))

    case EAdd(left, right) =>
      checkNum(left, tenv); checkNum(right, tenv); NumT
    case EMul(left, right) =>
      checkNum(left, tenv); checkNum(right, tenv); NumT
    case EDiv(left, right) =>
      checkNum(left, tenv); checkNum(right, tenv); NumT
    case EMod(left, right) =>
      checkNum(left, tenv); checkNum(right, tenv); NumT

    case EConcat(left, right) =>
      checkStr(left, tenv); checkStr(right, tenv); StrT

    case EEq(left, right) =>
      typeCheck(left, tenv); typeCheck(right, tenv); BoolT
    case ELt(left, right) =>
      checkNum(left, tenv); checkNum(right, tenv); BoolT

    case ESeq(left, right) =>
      typeCheck(left, tenv)
      typeCheck(right, tenv)

    case EIf(cond, thenExpr, elseExpr) =>
      checkBool(cond, tenv)
      join(typeCheck(thenExpr, tenv), typeCheck(elseExpr, tenv))

    case EVal(x, tyOpt, expr, body) =>
      val tExpr = typeCheck(expr, tenv)
      val tVal = tyOpt match {
        case Some(t) => 
          checkValidType(t, tenv)
          if (!subtype(tExpr, t)) error("Type mismatch")
          t
        case None => tExpr
      }
      typeCheck(body, tenv.addVar(x, tVal))

    case EFun(params, body) =>
      val paramNames = params.map(_.name)
      if (paramNames.distinct.length != paramNames.length) error("Duplicate parameters")
      
      params.foreach(p => checkValidType(p.ty, tenv))

      val newTenv = tenv.addVars(params.map(p => p.name -> p.ty))
      val tBody = typeCheck(body, newTenv)
      ArrowT(Nil, params.map(_.ty), tBody)

    case EApp(fun, tys, args) =>
      tys.foreach(checkValidType(_, tenv))

      val tFun = typeCheck(fun, tenv)
      tFun match {
        case ArrowT(tvars, paramTys, retTy) =>
          if (tvars.length != tys.length) error("type argument count mismatch")
          if (paramTys.length != args.length) error("argument count mismatch")
          
          val substitution = tvars.zip(tys).toMap
          val expectedTypes = paramTys.map(subst(_, substitution))
          
          args.zip(expectedTypes).foreach { case (arg, expected) =>
            val tArg = typeCheck(arg, tenv)
            if (!subtype(tArg, expected)) error("argument type mismatch")
          }
          
          subst(retTy, substitution)
        case _ => error("nat a function")
      }

    case ERecDefs(defs, body) =>
      val tenv1 = defs.foldLeft(tenv) {
        case (env, TypeDef(name, tvars, variants)) =>
          if (env.tys.contains(name)) error("Duplicate type name")
          tvars.foreach(tv => if (env.tys.contains(tv)) error("shadowing type"))
          env.addTypeName(name, tvars, variants)
        case (env, _) => env
      }

      val tenv2 = defs.foldLeft(tenv1) {
        case (env, LazyVal(name, ty, _)) =>
          if (env.vars.contains(name)) error("duplicate definition")
          checkValidType(ty, tenv1)
          env.addVar(name, ty)
        
        case (env, RecFun(name, tvars, params, rty, _)) =>
          if (env.vars.contains(name)) error("duplicate definition")
          val funType = ArrowT(tvars, params.map(_.ty), rty)
          checkValidType(funType, tenv1) 
          env.addVar(name, funType)
        
        case (env, TypeDef(typeName, tvars, variants)) =>
          variants.foldLeft(env) { (accEnv, variant) =>
            if (accEnv.vars.contains(variant.name)) error("duplicate constructor")
            val consType = ArrowT(tvars, variant.params.map(_.ty), IdT(typeName, tvars.map(tv => IdT(tv))))
            accEnv.addVar(variant.name, consType)
          }
      }

      defs.foreach {
        case LazyVal(name, ty, expr) =>
          val tExpr = typeCheck(expr, tenv2)
          if (!subtype(tExpr, ty)) error("LazyVal type mismatch")
        case RecFun(name, tvars, params, rty, body) =>
          val bodyEnv = tenv2.addTypeVars(tvars).addVars(params.map(p => p.name -> p.ty))
          val tBody = typeCheck(body, bodyEnv)
          if (!subtype(tBody, rty)) error("RecFun return type mismatch")
        case TypeDef(name, tvars, variants) =>
          val typeEnv = tenv2.addTypeVars(tvars)
          variants.foreach { variant =>
             variant.params.foreach(p => checkValidType(p.ty, typeEnv))
          }
      }

      val bodyType = typeCheck(body, tenv2)
      checkValidType(bodyType, tenv)
      bodyType

    case EMatch(expr, mcases) =>
      val tExpr = typeCheck(expr, tenv)
      tExpr match {
        case IdT(typeName, typeArgs) =>
          val typeInfo = tenv.tys.getOrElse(typeName, error("Unknown type"))
          typeInfo match {
            case TIAdt(tvars, variants) =>
              if (tvars.length != typeArgs.length) error("type args mismatch")
              val typeMapping = tvars.zip(typeArgs).toMap

              val caseNames = mcases.map(_.name)
              if (caseNames.distinct.length != caseNames.length) error("duplicate case")

              val allVariantNames = variants.keySet
              val coveredNames = caseNames.toSet
              if (allVariantNames != coveredNames) {
                val missing = (allVariantNames -- coveredNames).head
                error("missing case")
              }
              
              val caseTypes = mcases.map { case MatchCase(name, params, body) =>
                val variantParams = variants.getOrElse(name, error("Unknown variant"))
                if (params.length != variantParams.length) error("???")
                
                val substParams = variantParams.map(p => subst(p.ty, typeMapping))
                val caseEnv = tenv.addVars(params.zip(substParams))
                
                typeCheck(body, caseEnv)
              }
              
              if (caseTypes.isEmpty) NothingT else caseTypes.reduce(join)
            case _ => error("???")
          }
        case _ => error("invalid type pattern")
      }

    case EExit(expr) =>
      typeCheck(expr, tenv)
      NothingT
  }

  private def checkNum(e: Expr, env: TypeEnv): Unit = 
    if (!subtype(typeCheck(e, env), NumT)) error("not number")
  private def checkBool(e: Expr, env: TypeEnv): Unit = 
    if (!subtype(typeCheck(e, env), BoolT)) error("not boolean")
  private def checkStr(e: Expr, env: TypeEnv): Unit = 
    if (!subtype(typeCheck(e, env), StrT)) error("string")

  def interp(expr: Expr, env: Env): Value = expr match {
    case EUnit => UnitV
    case ENum(n) => NumV(n)
    case EBool(b) => BoolV(b)
    case EStr(s) => StrV(s)
    
    case EId(name) =>
      val v = env.getOrElse(name, error("Unbound variable"))
      v match {
        case ExprV(e, envThunk) => interp(e, envThunk())
        case _ => v
      }

    case EAdd(l, r) => (interp(l, env), interp(r, env)) match {
      case (NumV(n1), NumV(n2)) => NumV(n1 + n2)
      case _ => error("not numbers?")
    }
    case EMul(l, r) => (interp(l, env), interp(r, env)) match {
      case (NumV(n1), NumV(n2)) => NumV(n1 * n2)
      case _ => error("not numbers?")
    }
    case EDiv(l, r) => (interp(l, env), interp(r, env)) match {
      case (NumV(n1), NumV(n2)) => if (n2 == 0) error("Division by zero") else NumV(n1 / n2)
      case _ => error("not numbers?")
    }
    case EMod(l, r) => (interp(l, env), interp(r, env)) match {
      case (NumV(n1), NumV(n2)) => if (n2 == 0) error("Modulo by zero") else NumV(n1 % n2)
      case _ => error("not numbers?")
    }
    case EConcat(l, r) => (interp(l, env), interp(r, env)) match {
      case (StrV(s1), StrV(s2)) => StrV(s1 + s2)
      case _ => error("not strings?")
    }
    
    case EEq(l, r) => BoolV(eq(interp(l, env), interp(r, env)))
    
    case ELt(l, r) => (interp(l, env), interp(r, env)) match {
      case (NumV(n1), NumV(n2)) => BoolV(n1 < n2)
      case _ => error("Less-than expects numbers")
    }

    case ESeq(l, r) => 
      interp(l, env)
      interp(r, env)

    case EIf(cond, t, e) => interp(cond, env) match {
      case BoolV(true) => interp(t, env)
      case BoolV(false) => interp(e, env)
      case _ => error("not boolean")
    }

    case EVal(x, _, e, body) =>
      val v = interp(e, env)
      interp(body, env + (x -> v))

    case EFun(params, body) =>
      CloV(params.map(_.name), body, () => env)

    case EApp(fun, _, args) =>
      val fVal = interp(fun, env)
      val argVals = args.map(interp(_, env))
      fVal match {
        case CloV(params, body, fEnv) =>
          if (params.length != argVals.length) error("argument count mismatch")
          interp(body, fEnv() ++ params.zip(argVals))
        case ConstrV(name) =>
          VariantV(name, argVals)
        case _ => error("???")
      }

    case ERecDefs(defs, body) =>
      lazy val newEnv: Env = env ++ defs.flatMap {
        case LazyVal(name, _, expr) => 
          Some(name -> ExprV(expr, () => newEnv))
        case RecFun(name, _, params, _, body) => 
          Some(name -> CloV(params.map(_.name), body, () => newEnv))
        case TypeDef(name, _, variants) =>
          variants.map(v => v.name -> ConstrV(v.name))
      }
      interp(body, newEnv)

    case EMatch(expr, mcases) =>
      val v = interp(expr, env)
      v match {
        case VariantV(name, values) =>
          mcases.find(_.name == name) match {
            case Some(MatchCase(_, params, body)) =>
              if (params.length != values.length) error("???")
              interp(body, env ++ params.zip(values))
            case None => error("no matching case")
          }
        case _ => error("matching non-variant value")
      }

    case EExit(expr) =>
      val msg = interp(expr, env).str
      error("Program die")
  }

  private def eq(v1: Value, v2: Value): Boolean = (v1, v2) match {
    case (UnitV, UnitV) => true
    case (NumV(n1), NumV(n2)) => n1 == n2
    case (BoolV(b1), BoolV(b2)) => b1 == b2
    case (StrV(s1), StrV(s2)) => s1 == s2
    case (VariantV(n1, vs1), VariantV(n2, vs2)) => 
      n1 == n2 && vs1.length == vs2.length && vs1.zip(vs2).forall { case (a, b) => eq(a, b) }
    case _ => false
  }
}