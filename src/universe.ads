with Ada.Numerics.Big_Numbers.Big_Reals;
use Ada.Numerics.Big_Numbers.Big_Reals;
with Spatial;
with Vector;

generic
   Max_Items : Positive;

package Universe with SPARK_Mode is

   use type Spatial.Position;
   use type Spatial.Velocity;
   use type Vector.Vector;

   type Universe is private;

   function Item_Count (U : Universe) return Integer;

   function Get_Position
     (U : Universe; Index : Integer) return Spatial.Position
     with Pre => Index >= 1 and then Index <= Item_Count (U);

   function Get_Velocity
     (U : Universe; Index : Integer) return Spatial.Velocity
     with Pre => Index >= 1 and then Index <= Item_Count (U);

   function Get_Radius
     (U : Universe; Index : Integer) return Big_Real
     with Pre => Index >= 1 and then Index <= Item_Count (U);


   procedure Init (U : out Universe);
   --  TODO: add postcondition

   procedure Add_Item
     (U   : in out Universe;
      pos : Spatial.Position;
      vel : Spatial.Velocity;
      rad : Big_Real)
     with
       Pre  => Item_Count (U) < Max_Items;
   --  TODO: add postcondition

   procedure Tick (U : in out Universe);
   --  TODO: add postcondition

   procedure Reflect_Velocity_X
     (U : in out Universe; Index : Integer)
     with
       Pre  => Index >= 1 and then Index <= Item_Count (U),
       Post =>
         Item_Count (U) = Item_Count (U'Old)
         and then Get_Velocity (U, Index) =
           Spatial.Negate_Vel_X (Get_Velocity (U'Old, Index))
         and then
           (for all I in 1 .. Item_Count (U) =>
              Get_Position (U, I) = Get_Position (U'Old, I)
              and then Get_Radius (U, I) = Get_Radius (U'Old, I)
              and then (if I /= Index then
                Get_Velocity (U, I) = Get_Velocity (U'Old, I)));

   procedure Reflect_Velocity_Y
     (U : in out Universe; Index : Integer)
     with
       Pre  => Index >= 1 and then Index <= Item_Count (U),
       Post =>
         Item_Count (U) = Item_Count (U'Old)
         and then Get_Velocity (U, Index) =
           Spatial.Negate_Vel_Y (Get_Velocity (U'Old, Index))
         and then
           (for all I in 1 .. Item_Count (U) =>
              Get_Position (U, I) = Get_Position (U'Old, I)
              and then Get_Radius (U, I) = Get_Radius (U'Old, I)
              and then (if I /= Index then
                Get_Velocity (U, I) = Get_Velocity (U'Old, I)));

   procedure Print (U : Universe)
     with SPARK_Mode => Off;

private
   type Universe_Item is record
      pos : Spatial.Position;
      vel : Spatial.Velocity;
      rad : Big_Real;
   end record;

   type ItemArray is
     array (Integer range 1 .. Max_Items) of Universe_Item;

   type Universe is record
      items          : ItemArray;
      item_count     : Integer range 0 .. Max_Items;
   end record;

   function Item_Count
     (U : Universe) return Integer is (U.item_count);

   function Get_Position
     (U : Universe; Index : Integer)
      return Spatial.Position is (U.items (Index).pos);

   function Get_Velocity
     (U : Universe; Index : Integer)
      return Spatial.Velocity is (U.items (Index).vel);

   function Get_Radius
     (U : Universe; Index : Integer)
      return Big_Real is (U.items (Index).rad);

end Universe;
