with Ada.Numerics.Big_Numbers.Big_Reals;
--  Import arbitrary-precision real numbers used for radii and coordinates.
use Ada.Numerics.Big_Numbers.Big_Reals;
--  Make Big_Real names directly visible in this spec.
with Spatial;
--  Position/velocity domain-specific types and motion helpers.
with Vector;
--  Underlying 2D vector representation and operations.

--  TASK 1 — read preconditions on Get_*, Add_Item, Tick, Reflect_* below.
--  TASK 2 — Init and Add_Item contracts; implement bodies in universe.adb.
--  TASK 3 — Tick contract; implement body (with loop invariants) in universe.adb.

generic
   Max_Items : Positive;
   --  Compile-time maximum capacity of the universe.

package Universe with SPARK_Mode is
   --  Public API for a bounded collection of moving circular items.

   use type Spatial.Position;
   --  Enable equality/ordering use for Position in contracts.
   use type Spatial.Velocity;
   --  Enable equality/ordering use for Velocity in contracts.
   use type Vector.Vector;
   --  Enable vector comparisons in proofs/contracts when needed.

   type Universe is private;
   --  Clients can use Universe values but cannot access representation.

   function Item_Count (U : Universe) return Integer;
   --  Number of active items currently stored.

   function Get_Position
     (U : Universe; Index : Integer) return Spatial.Position
     with Pre => Index >= 1 and then Index <= Item_Count (U);
   --  Read position for an active item.
   --  Pre ensures Index refers to the initialized active prefix.

   function Get_Velocity
     (U : Universe; Index : Integer) return Spatial.Velocity
     with Pre => Index >= 1 and then Index <= Item_Count (U);
   --  Read velocity for an active item.
   --  Same safety precondition as Get_Position.

   function Get_Radius
     (U : Universe; Index : Integer) return Big_Real
     with Pre => Index >= 1 and then Index <= Item_Count (U);
   --  Read radius for an active item.
   --  Same safety precondition as Get_Position.


   procedure Init (U : out Universe)
     with
       Post => Item_Count (U) = 0;
   --  Reinitialize universe to empty state.
   --  Post guarantees no active items after Init.

   procedure Add_Item
     (U   : in out Universe;
      pos : Spatial.Position;
      vel : Spatial.Velocity;
      rad : Big_Real)
     with
       Pre  => Item_Count (U) < Max_Items,
       Post =>
         --  1) Item count increases by exactly one.
         Item_Count (U) = Item_Count (U'Old) + 1
         --  2) Newly appended item stores provided position.
         and then Get_Position (U, Item_Count (U)) = pos
         --  3) Newly appended item stores provided velocity.
         and then Get_Velocity (U, Item_Count (U)) = vel
         --  4) Newly appended item stores provided radius.
         and then Get_Radius   (U, Item_Count (U)) = rad
         --  5) Previously existing items are unchanged.
         and then (for all I in 1 .. Item_Count (U'Old) =>
                     Get_Position (U, I) = Get_Position (U'Old, I)
                     and then Get_Velocity (U, I) = Get_Velocity (U'Old, I)
                     and then Get_Radius   (U, I) = Get_Radius   (U'Old, I));
   --  Append operation with frame condition over old items.

   procedure Tick (U : in out Universe)
     with
       Post =>
         --  1) Tick does not create/remove items.
         Item_Count (U) = Item_Count (U'Old)
         --  2) For each item: position advances by one velocity step,
         --     while velocity and radius are preserved.
         and then (for all I in 1 .. Item_Count (U) =>
                     Get_Position (U, I) =
                       Spatial.Move (Get_Position (U'Old, I),
                                     Get_Velocity (U'Old, I))
                     and then Get_Velocity (U, I) = Get_Velocity (U'Old, I)
                     and then Get_Radius   (U, I) = Get_Radius   (U'Old, I));
   --  Discrete-time dynamics for one frame.

   procedure Reflect_Velocity_X
     (U : in out Universe; Index : Integer)
     with
       Pre  => Index >= 1 and then Index <= Item_Count (U),
       Post =>
         --  1) Item count unchanged.
         Item_Count (U) = Item_Count (U'Old)
         --  2) Selected velocity has X component negated.
         and then Get_Velocity (U, Index) =
           Spatial.Negate_Vel_X (Get_Velocity (U'Old, Index))
         and then
           --  3) For all items, position/radius unchanged,
           --     and non-selected velocities unchanged.
           (for all I in 1 .. Item_Count (U) =>
              Get_Position (U, I) = Get_Position (U'Old, I)
              and then Get_Radius (U, I) = Get_Radius (U'Old, I)
              and then (if I /= Index then
                Get_Velocity (U, I) = Get_Velocity (U'Old, I)));
   --  Used for horizontal wall bounces.

   procedure Reflect_Velocity_Y
     (U : in out Universe; Index : Integer)
     with
       Pre  => Index >= 1 and then Index <= Item_Count (U),
       Post =>
         --  1) Item count unchanged.
         Item_Count (U) = Item_Count (U'Old)
         --  2) Selected velocity has Y component negated.
         and then Get_Velocity (U, Index) =
           Spatial.Negate_Vel_Y (Get_Velocity (U'Old, Index))
         and then
           --  3) For all items, position/radius unchanged,
           --     and non-selected velocities unchanged.
           (for all I in 1 .. Item_Count (U) =>
              Get_Position (U, I) = Get_Position (U'Old, I)
              and then Get_Radius (U, I) = Get_Radius (U'Old, I)
              and then (if I /= Index then
                Get_Velocity (U, I) = Get_Velocity (U'Old, I)));
   --  Used for vertical wall bounces.

   procedure Print (U : Universe)
     with SPARK_Mode => Off;
   --  Debug output helper (I/O is outside SPARK proof subset).

private
   type Universe_Item is record
      pos : Spatial.Position;
      --  Current position in arena coordinates.
      vel : Spatial.Velocity;
      --  Per-tick displacement.
      rad : Big_Real;
      --  Circle radius for collision threshold checks.
   end record;

   type ItemArray is
     array (Integer range 1 .. Max_Items) of Universe_Item;
   --  Fixed-capacity storage; only prefix 1 .. item_count is active.

   type Universe is record
      items          : ItemArray;
      --  Backing array for all potential items.
      item_count     : Integer range 0 .. Max_Items;
      --  Number of active initialized items.
   end record;

   function Item_Count
     (U : Universe) return Integer is (U.item_count);
   --  Simple accessor function body.

   function Get_Position
     (U : Universe; Index : Integer)
      return Spatial.Position is (U.items (Index).pos);
   --  Direct field accessor; precondition is declared in public part.

   function Get_Velocity
     (U : Universe; Index : Integer)
      return Spatial.Velocity is (U.items (Index).vel);
   --  Direct field accessor; precondition is declared in public part.

   function Get_Radius
     (U : Universe; Index : Integer)
      return Big_Real is (U.items (Index).rad);
   --  Direct field accessor; precondition is declared in public part.

end Universe;
